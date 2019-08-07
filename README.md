# An HTTP frontend for CVC4

[![Build Status](https://travis-ci.org/stanford-oval/cvc4-http-server.svg?branch=master)](https://travis-ci.com/stanford-oval/cvc4-http-server)

[CVC4](https://cvc4.cs.stanford.edu) is a powerful Satisfiability Modulo Theories (SMT) solver and theorem prover
developed. This package provides an HTTP frontend server that allows to serve SMT requests using CVC4.

## Dependencies

This package depends on the CVC4 libraries (version 1.5 or 1.6, **not 1.7**), on libsoup, and on the meson
build system.

On Ubuntu 18.04, you can install the dependencies with:
```bash
sudo apt install -y cvc4 libcvc4-dev libsoup2.4-dev libcln-dev meson ninja-build
```

## Installation

```bash
meson build
ninja -C build
sudo ninja -C build install
```

You can then run the server as `/usr/local/bin/cvc4-http-server`, and issue requests to `https://127.0.0.1:8400/solve`.
Requests should be raw SMT-Lib 2.0 files, starting with a `(set-logic)` command, and terminating with `(check-sat)` or `(get-model)`.
By default the server listens on port 8400; set the `PORT` environment variable to change it.

The server does not support TLS; use a reverse proxy such as Apache or nginx instead.

## License

This package is covered by the GNU General Public License, version 2
or any later version. See [COPYING](COPYING) for details.
