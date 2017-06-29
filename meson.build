project('cvc4-http-server', 'cpp',
  version: '0.0.1',
  meson_version: '>= 0.36.0',
  license: ['GPLv2+']
)

intl = import('i18n')

config_h = configuration_data()
GETTEXT_PACKAGE = meson.project_name()
config_h.set_quoted('GETTEXT_PACKAGE', GETTEXT_PACKAGE)
config_h.set_quoted('LOCALEDIR', join_paths(get_option('prefix'), get_option('localedir')))
configure_file(
  output: 'config.h',
  configuration: config_h,
)
add_global_arguments([
  '-DHAVE_CONFIG_H',
  '-I' + meson.build_root(),
], language: 'cpp')

subdir('src')
subdir('po')
