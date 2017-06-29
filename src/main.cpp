/*
  cvc4-http-server: an HTTP API over CVC4
  Copyright 2017 Giovanni Campagna <gcampagn@cs.stanford.edu>

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
*/

#include <algorithm>
#include <cstdlib>

#include <glib.h>

#include "request.hpp"
#include "server.hpp"

namespace cvc4_http {
    struct gmain_copy_ops {
         static void ref(GMainLoop* loop) {
             g_main_loop_ref(loop);
         }
         static void unref(GMainLoop* loop) {
             g_main_loop_unref(loop);
         }
    };
}

int main() {
    cvc4_http::Server server;

    cvc4_http::gref_ptr<GMainLoop, cvc4_http::gmain_copy_ops> loop(g_main_loop_new (nullptr, false));
    g_main_loop_run(loop.get());
    return 0;
}
