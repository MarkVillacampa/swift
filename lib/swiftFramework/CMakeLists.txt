add_swift_library(swiftFramework SHARED
  api_notes.cpp
  driver.cpp
  autolink_extract_main.cpp
  modulewrap_main.cpp
  swift_format_main.cpp
  Immediate.cpp
  LINK_LIBRARIES
    swiftDriver
    swiftFrontendTool
  LLVM_COMPONENT_DEPENDS
    DebugInfoCodeView
)

swift_install_in_component(compiler
    TARGETS swiftFramework
    LIBRARY DESTINATION "lib${LLVM_LIBDIR_SUFFIX}"
    ARCHIVE DESTINATION "lib${LLVM_LIBDIR_SUFFIX}")
