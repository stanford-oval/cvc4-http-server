FROM ubuntu:18.04

RUN apt-get update -q -y
RUN apt-get install -y cvc4 libcvc4-dev libsoup2.4-dev libcln-dev build-essential meson ninja-build git gettext
RUN git clone https://github.com/stanford-oval/cvc4-http-server
WORKDIR cvc4-http-server
RUN meson build --prefix=/usr/local
RUN ninja -C build
RUN ninja -C build install

ENV PORT=8400
ENTRYPOINT ["/usr/local/bin/cvc4-http-server"]
