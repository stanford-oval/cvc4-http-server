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

#include <libsoup/soup.h>

#include "refptr.hpp"

namespace cvc4_http {

class Request {
private:
    gref_ptr<SoupMessage> message;
    gboxed_ptr<SoupClientContext, soup_client_context_get_type> client_context;

public:
    Request(SoupMessage* msg, SoupClientContext *client_context) :
        message(make_gref_ptr(msg, false)),
        client_context(client_context, false)
        {}

    gref_ptr<SoupMessage> get_message() const {
        return message;
    }

    const gboxed_ptr<SoupClientContext, soup_client_context_get_type>& get_context() const {
        return client_context;
    }
};

}
