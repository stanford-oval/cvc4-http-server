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
#include <iostream>
#include <functional>

#include "server.hpp"
#include "gexcept.hpp"
#include "solver.hpp"

#define DEFAULT_PORT 8400

namespace cvc4_http {

unsigned get_port()
{
    const char *port = std::getenv("PORT");
    if (port == nullptr)
        return DEFAULT_PORT;
    return (unsigned) std::strtoul (port, nullptr, 10);
}

Server::Server() : server(soup_server_new("server-header", "cvc4-http-server/0.0.1", nullptr)), thread_pool(16) {
    unsigned port = get_port();
    std::cout << "Using port " << port << std::endl;

    gtry_catch try_catch;
    soup_server_listen_all (server.get(), port, (SoupServerListenOptions)0, try_catch);
    try_catch.check();

    soup_server_add_handler (server.get(), "/solve", [](SoupServer *server, SoupMessage *msg, const char *path, GHashTable *query, SoupClientContext *client, void *user_data) {
        Server *self = static_cast<Server*>(user_data);
        Request request(msg, client);
        self->handle_solve(std::move(request));
    }, this, nullptr);
}

void Server::handle_solve(Request&& req) {
    auto message = req.get_message();

    struct task {
        Server *server;
        std::shared_ptr<Request> req;
        std::shared_ptr<soup_message_stream> stream;

        task(Server *self, Request&& req_) :
            server(self),
            req(new Request(std::move(req_))),
            stream(new soup_message_stream(server->server, req->get_message())) {}

        void operator()(Solver& solver) {
            server->do_handle_solve(solver, *req, *stream);
        }
    };

    soup_message_set_status(message.get(), 200);
    thread_pool.push(task(this, std::move(req)));
}

void Server::do_handle_solve(Solver& solver, const Request& req, soup_message_stream& stream)
{
    auto message = req.get_message();
    auto istream = std::stringstream(std::string(message->request_body->data, message->request_body->length));
    std::ostream ostream(&stream);

    try {
        solver.process(istream, ostream);
    } catch(CVC4::Exception& e) {
        std::cerr << "CVC4 Error: " << e.what() << std::endl;
    } catch(gexception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
    }
}

}
