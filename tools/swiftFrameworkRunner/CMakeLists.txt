add_swift_host_tool(swiftFrameworkRunner
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
  SWIFT_COMPONENT compiler
)

if(HAVE_UNICODE_LIBEDIT)
  target_link_libraries(swiftFrameworkRunner edit)
endif()

swift_install_in_component(compiler
    FILES "${SWIFT_RUNTIME_OUTPUT_INTDIR}/swiftFrameworkRunner"
    DESTINATION "bin")
