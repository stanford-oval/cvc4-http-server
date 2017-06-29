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

#pragma once
#include <libsoup/soup.h>

#include "refptr.hpp"
#include "request.hpp"
#include "threadpool.hpp"
#include "soup_stream.hpp"
#include "solver.hpp"

namespace cvc4_http {

class Server {
private:
    gref_ptr<SoupServer> server;
    threadpool<Solver> thread_pool;

    void handle_solve(Request&& req);
    void do_handle_solve(Solver &solver, const Request& req, soup_message_stream& ostreambuf);

public:
    Server();
};

}
