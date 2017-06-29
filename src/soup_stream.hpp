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
#include <memory>
#include <streambuf>

#include <libsoup/soup.h>

namespace cvc4_http {

class soup_message_stream : public std::streambuf {
private:
    gref_ptr<SoupServer> server;
    gref_ptr<SoupMessage> message;
    std::unique_ptr<char[]> buffer;
    static const size_t buffer_size = 1023;

    template<class Callable>
    class gidle_caller {
    private:
        Callable f;

        static gboolean do_call(void *user_data) {
            gidle_caller *self = static_cast<gidle_caller*>(user_data);
            self->f();
            delete self;
            return G_SOURCE_REMOVE;
        }

        gidle_caller(Callable&& c) :
            f(std::forward<Callable>(c)) {}

    public:
        static void schedule(Callable&& c) {
            gidle_caller<Callable> *self = new gidle_caller<Callable>(std::forward<Callable>(c));
            g_idle_add(do_call, self);
        };
    };

    template<class Callable>
    static void idle_schedule(Callable&& c) {
        gidle_caller<Callable>::schedule(std::forward<Callable>(c));
    }

    void flush(size_t size, bool set_new_buffer = true)
    {
        if (size == 0)
            return;

        std::unique_ptr<char[]> copy;

        if (set_new_buffer) {
            copy.reset(new char[buffer_size+1]);
            std::swap(copy, buffer);
            setp(buffer.get(), buffer.get()+buffer_size);
        } else {
            std::swap(copy, buffer);
            setp(nullptr, nullptr);
        }

        struct append_buffer {
            std::unique_ptr<char[]> buf;
            gref_ptr<SoupServer> server;
            gref_ptr<SoupMessage> message;
            size_t size;

            void operator()() {
                soup_message_body_append_take(message->response_body, (guchar*)buf.release(), size);
                soup_server_unpause_message(server.get(), message.get());
            }
        };
        idle_schedule(append_buffer { std::move(copy), server, message, size });
    }

public:
    soup_message_stream(const gref_ptr<SoupServer>& server_,
                        const gref_ptr<SoupMessage>& msg) :
        server(server_),
        message(msg),
        buffer(new char[buffer_size+1])
    {
        soup_message_headers_set_encoding(message->response_headers, SOUP_ENCODING_CHUNKED);
        setp(buffer.get(), buffer.get()+buffer_size);
    }
    soup_message_stream(const soup_message_stream&) = delete;
    soup_message_stream(soup_message_stream&& o) = default;

    virtual ~soup_message_stream() {
        flush(pptr()-pbase(), false);

        idle_schedule(std::bind([](gref_ptr<SoupServer> server, gref_ptr<SoupMessage> message) {
            soup_message_body_complete(message->response_body);
            soup_server_unpause_message(server.get(), message.get());
        }, server, message));
    }

    virtual int sync() override {
        flush(pptr()-pbase());
        return 0;
    }

    virtual int_type overflow(int_type ch) override {
        if (ch == traits_type::eof()) {
            flush(pptr()-pbase());
            return 0;
        }
        buffer[buffer_size] = ch;
        flush(buffer_size+1);
        return ch;
    }
};

}
