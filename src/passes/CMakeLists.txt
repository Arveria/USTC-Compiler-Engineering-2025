add_library(
    passes STATIC
    DeadCode.cpp
    Dominators.cpp
    FuncInfo.cpp
    Mem2Reg.cpp
    ConstPropagation.cpp
    FunctionInline.cpp
)

target_link_libraries(passes common)