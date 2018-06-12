//===--- driver.cpp - Swift Compiler Driver -------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// This is the entry point to the swift compiler driver.
//
//===----------------------------------------------------------------------===//

#include "swift/Immediate/Immediate.h"
#include "ImmediateImpl.h"

#include "swift/Subsystems.h"
#include "swift/AST/DiagnosticEngine.h"
#include "swift/AST/DiagnosticsFrontend.h"
#include "swift/Basic/LLVMContext.h"
#include "swift/Basic/LLVMInitialize.h"
#include "swift/Basic/Program.h"
#include "swift/Basic/SourceManager.h"
#include "swift/Driver/Compilation.h"
#include "swift/Driver/Driver.h"
#include "swift/Driver/FrontendUtil.h"
#include "swift/Driver/Job.h"
#include "swift/Frontend/Frontend.h"
#include "swift/Frontend/PrintingDiagnosticConsumer.h"
#include "swift/FrontendTool/FrontendTool.h"
#include "swift/Immediate/Immediate.h"
#include "swift/SILOptimizer/PassManager/Passes.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ExecutionEngine/MCJIT.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"

#include <memory>
#include <stdlib.h>

using namespace swift;
using namespace swift::driver;
using namespace swift::immediate;

class REPLContext {
public:
  /// The SourceMgr buffer ID of the REPL input.
  unsigned CurBufferID;
  
  /// The index into the source file's Decls at which to start
  /// typechecking the next REPL input.
  unsigned CurElem;

  /// The index into the source file's Decls at which to start
  /// irgenning the next REPL input.
  unsigned CurIRGenElem;
};

llvm::StringSet<> FuncsAlreadyGenerated;
llvm::StringSet<> GlobalsAlreadyEmitted;

std::string getExecutablePath(const char *FirstArg) {
  void *P = (void *)(intptr_t)getExecutablePath;
  return llvm::sys::fs::getMainExecutable(FirstArg, P);
}

extern int apinotes_main(ArrayRef<const char *> Args);

static bool appendToREPLFile(SourceFile &SF,
                             PersistentParserState &PersistentState,
                             REPLContext &RC,
                             std::unique_ptr<llvm::MemoryBuffer> Buffer) {
  assert(SF.Kind == SourceFileKind::REPL && "Can't append to a non-REPL file");

  SourceManager &SrcMgr = SF.getParentModule()->getASTContext().SourceMgr;
  RC.CurBufferID = SrcMgr.addNewSourceBuffer(std::move(Buffer));

  bool FoundAnySideEffects = false;
  unsigned CurElem = RC.CurElem;
  bool Done;
  do {
    FoundAnySideEffects |=
        parseIntoSourceFile(SF, RC.CurBufferID, &Done, nullptr,
                            &PersistentState);
    performTypeChecking(SF, PersistentState.getTopLevelContext(), None,
                        CurElem);
    CurElem = SF.Decls.size();
  } while (!Done);
  return FoundAnySideEffects;
}

void stripPreviouslyGenerated(llvm::Module &M) {
  for (auto &function : M.getFunctionList()) {
    function.setVisibility(llvm::GlobalValue::DefaultVisibility);
    if (FuncsAlreadyGenerated.count(function.getName()))
      function.deleteBody();
    else {
      if (function.getName() != SWIFT_ENTRY_POINT_FUNCTION)
        FuncsAlreadyGenerated.insert(function.getName());
    }
  }

  for (auto &global : M.globals()) {
    if (!global.hasName())
      continue;
    if (global.hasGlobalUnnamedAddr())
      continue;

    global.setVisibility(llvm::GlobalValue::DefaultVisibility);
    if (!global.hasAvailableExternallyLinkage() &&
        !global.hasAppendingLinkage() &&
        !global.hasCommonLinkage()) {
      global.setLinkage(llvm::GlobalValue::ExternalLinkage);
      if (GlobalsAlreadyEmitted.count(global.getName()))
        global.setInitializer(nullptr);
      else
        GlobalsAlreadyEmitted.insert(global.getName());
    }
  }


  for (auto alias = M.alias_begin(); alias != M.alias_end();) {
    alias->setVisibility(llvm::GlobalValue::DefaultVisibility);
    if (!alias->hasAvailableExternallyLinkage() &&
        !alias->hasAppendingLinkage() &&
        !alias->hasCommonLinkage()) {
      alias->setLinkage(llvm::GlobalValue::ExternalLinkage);
      if (GlobalsAlreadyEmitted.count(alias->getName())) {
        // Replace already-emitted aliases with external declarations.
        SmallString<32> name = alias->getName();
        alias->setName("");
        auto external = new llvm::GlobalVariable(
          M,
          alias->getType()->getPointerElementType(),
          /*isConstant*/ false,
          alias->getLinkage(),
          /*initializer*/ nullptr,
          name);
        alias->replaceAllUsesWith(external);
        auto &aliasToRemove = *alias;
        ++alias;
        aliasToRemove.eraseFromParent();
      } else {
        GlobalsAlreadyEmitted.insert(alias->getName());
        ++alias;
      }
    }
  }
}

int main(int argc_, const char **argv_) {
  INITIALIZE_LLVM(argc_, argv_);
  llvm::InitializeAllTargets();
  llvm::InitializeAllTargetMCs();
  llvm::InitializeAllAsmPrinters();
  llvm::InitializeAllAsmParsers();

  SmallVector<const char *, 256> argv;
  llvm::SpecificBumpPtrAllocator<char> ArgAllocator;
  std::error_code EC = llvm::sys::Process::GetArgumentVector(
      argv, llvm::ArrayRef<const char *>(argv_, argc_), ArgAllocator);
  if (EC) {
    llvm::errs() << "error: couldn't get arguments: " << EC.message() << '\n';
    return 1;
  }

  std::unique_ptr<CompilerInstance> Instance =
    llvm::make_unique<CompilerInstance>();

  CompilerInvocation Invocation;
  Invocation.setInputKind(InputFileKind::IFK_Swift_REPL);

  std::string MainExecutablePath = llvm::sys::fs::getMainExecutable(argv[0],
                                                                   (void *)(intptr_t)getExecutablePath);
  Invocation.setMainExecutablePath(MainExecutablePath);

  SmallString<128> workingDirectory;
  llvm::sys::fs::current_path(workingDirectory);

  ArrayRef<const char *> Args = llvm::makeArrayRef(argv.data()+2, argv.data()+argv.size());

  Invocation.parseArgs(Args, Instance->getDiags(), workingDirectory);
  Instance->setup(Invocation);
  Instance->performSema();

  /* return performFrontend(llvm::makeArrayRef(argv.data()+2, */
					    /* argv.data()+argv.size()), */
			 /* argv[0], (void *)(intptr_t)getExecutablePath); */


    /* runREPL(*Instance, ProcessCmdLine(Args.begin(), Args.end()), */
    /*         Invocation.getParseStdlib()); */

  CompilerInstance &CI = *Instance;
  SourceFile &REPLInputFile = CI.getMainModule()-> getMainSourceFile(SourceFileKind::REPL);
  ProcessCmdLine CmdLine(Args.begin(), Args.end());
  llvm::SmallPtrSet<swift::ModuleDecl *, 8> ImportedModules;
  SmallVector<llvm::Function*, 8> InitFns;
  bool RanGlobalInitializers = false;
  llvm::LLVMContext &LLVMContext = getGlobalLLVMContext();
  llvm::Module *Module(new llvm::Module("REPL", LLVMContext));
  llvm::Module DumpModule("REPL", LLVMContext);
  llvm::SmallString<128> DumpSource;
  llvm::ExecutionEngine *EE;
  IRGenOptions IRGenOpts = IRGenOptions();
  const SILOptions SILOpts = SILOptions();
  /* REPLInput Input; */
  REPLContext RC = {
    /*BufferID*/ 0U,
    /*CurElem*/ 0,
    /*CurIRGenElem*/ 0
  };
  PersistentParserState PersistentState;

  llvm::StringRef Line = "print(\"Hello world\")";

  ASTContext &Ctx = CI.getASTContext();
  if (!loadSwiftRuntime(Ctx.SearchPathOpts.RuntimeLibraryPath)) {
    CI.getDiags().diagnose(SourceLoc(),
                           diag::error_immediate_mode_missing_stdlib);
    assert(false);
  }
  tryLoadLibraries(CI.getLinkLibraries(), Ctx.SearchPathOpts, CI.getDiags());

  llvm::EngineBuilder builder{std::unique_ptr<llvm::Module>{Module}};
  std::string ErrorMsg;
  llvm::TargetOptions TargetOpt;
  std::string CPU;
  std::vector<std::string> Features;
  std::tie(TargetOpt, CPU, Features)
    = getIRTargetOptions(IRGenOpts, CI.getASTContext());

  builder.setRelocationModel(llvm::Reloc::PIC_);
  builder.setTargetOptions(TargetOpt);
  builder.setMCPU(CPU);
  builder.setMAttrs(Features);
  builder.setErrorStr(&ErrorMsg);
  builder.setEngineKind(llvm::EngineKind::JIT);
  EE = builder.create();

  IRGenOpts.OutputFilenames.clear();
  IRGenOpts.Optimize = false;
  IRGenOpts.OutputKind = IRGenOutputKind::Module;
  IRGenOpts.UseJIT = true;
  IRGenOpts.DebugInfoKind = IRGenDebugInfoKind::None;

  if (!Invocation.getParseStdlib()) {
    // Force standard library to be loaded immediately.  This forces any
    // errors to appear upfront, and helps eliminate some nasty lag after the
    // first statement is typed into the REPL.
    static const char WarmUpStmt[] = "Void()\n";

    auto Buffer =
        llvm::MemoryBuffer::getMemBufferCopy(WarmUpStmt,
                                             "<REPL Initialization>");
    appendToREPLFile(REPLInputFile, PersistentState, RC, std::move(Buffer));

    assert(!Ctx.hadError());
  }

  RC.CurElem = RC.CurIRGenElem = REPLInputFile.Decls.size();

  if (llvm::sys::Process::StandardInIsUserInput())
    llvm::outs() <<
        "***  You are running Swift's integrated REPL,  ***\n"
        "***  intended for compiler and stdlib          ***\n"
        "***  development and testing purposes only.    ***\n"
        "***  The full REPL is built as part of LLDB.   ***\n"
        "***  Type ':help' for assistance.              ***\n";



  // Parse the current line(s).
  auto InputBuf = std::unique_ptr<llvm::MemoryBuffer>(
      llvm::MemoryBuffer::getMemBufferCopy(Line, "<REPL Input>"));
  bool ShouldRun = appendToREPLFile(REPLInputFile, PersistentState, RC,
                                    std::move(InputBuf));

  // SILGen the module and produce SIL diagnostics.
  std::unique_ptr<SILModule> sil;

  if (!CI.getASTContext().hadError()) {
    sil = performSILGeneration(REPLInputFile, CI.getSILOptions(),
                               RC.CurIRGenElem);
    performSILLinking(sil.get());
    runSILDiagnosticPasses(*sil);
    runSILLoweringPasses(*sil);
  }

  if (CI.getASTContext().hadError()) {
    if (CI.getDiags().hasFatalErrorOccurred())
      return false;

    CI.getASTContext().Diags.resetHadAnyError();
    while (REPLInputFile.Decls.size() > RC.CurElem)
      REPLInputFile.Decls.pop_back();
    
    // FIXME: Handling of "import" declarations?  Is there any other
    // state which needs to be reset?
    
    return true;
  }

  RC.CurElem = REPLInputFile.Decls.size();

  DumpSource += Line;

  // If we didn't see an expression, statement, or decl which might have
  // side-effects, keep reading.
  if (!ShouldRun)
    return true;

  // IRGen the current line(s).
  // FIXME: We shouldn't need to use the global context here, but
  // something is persisting across calls to performIRGeneration.
  auto LineModule = performIRGeneration(IRGenOpts, REPLInputFile,
                                        std::move(sil),
                                        "REPLLine",
                                        getGlobalLLVMContext(),
                                        RC.CurIRGenElem);
  RC.CurIRGenElem = RC.CurElem;

  if (CI.getASTContext().hadError())
    return false;

  // LineModule will get destroy by the following link process.
  // Make a copy of it to be able to correct produce DumpModule.
  std::unique_ptr<llvm::Module> SaveLineModule(CloneModule(LineModule.get()));

  if (!linkLLVMModules(Module, std::move(LineModule))) {
    return false;
  }

  std::unique_ptr<llvm::Module> NewModule(CloneModule(Module));

  Module->getFunction("main")->eraseFromParent();

  stripPreviouslyGenerated(*NewModule);

  if (!linkLLVMModules(&DumpModule, std::move(SaveLineModule))) {
    return false;
  }
  llvm::Function *DumpModuleMain = DumpModule.getFunction("main");
  DumpModuleMain->setName("repl.line");

  if (IRGenImportedModules(CI, *NewModule, ImportedModules, InitFns,
                           IRGenOpts, SILOpts))
    return false;

  llvm::Module *TempModule = NewModule.get();
  EE->addModule(std::move(NewModule));

  EE->finalizeObject();

  for (auto InitFn : InitFns)
    EE->runFunctionAsMain(InitFn, CmdLine, nullptr);
  InitFns.clear();

  // FIXME: The way we do this is really ugly... we should be able to
  // improve this.
  if (!RanGlobalInitializers) {
    EE->runStaticConstructorsDestructors(*TempModule, false);
    RanGlobalInitializers = true;
  }
  llvm::Function *EntryFn = TempModule->getFunction("main");
  EE->runFunctionAsMain(EntryFn, CmdLine, nullptr);

  while(true){}
  return 0;
}
