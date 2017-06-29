cpp = meson.get_compiler('cpp')

executable('cvc4-http-server',
  ['main.cpp',
   'server.cpp',
   'solver.cpp'],
  dependencies: [
    dependency('cln'),
    cpp.find_library('cvc4'),
    cpp.find_library('cvc4parser'),
    dependency('libsoup-2.4'),
    dependency('threads')
  ]
)
