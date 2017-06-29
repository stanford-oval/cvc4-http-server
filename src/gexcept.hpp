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
#include <cstdarg>

#include <glib.h>

#include "refptr.hpp"

namespace cvc4_http {

struct gerror_deleter {
    void operator()(GError *err) const {
        g_error_free(err);
    }
};

class gexception {
private:
    std::unique_ptr<GError, gerror_deleter> error;

public:
    gexception(GError *err) : error(err) {}

    gexception(GQuark domain, int code, const gchar *format, ...) {
        va_list va;
        va_start(va, format);
        error = std::unique_ptr<GError, gerror_deleter>(g_error_new_valist(domain, code, format, va));
        va_end(va);
    }

    GError *get() const {
        return error.get();
    }

    GQuark get_domain() const {
        return error->domain;
    }
    int get_code() const {
        return error->code;
    }
    const char *get_message() const {
        return error->message;
    }
    const char *what() const {
        return error->message;
    }
};

class gtry_catch {
private:
    GError *storage = nullptr;

public:
    operator GError**() {
        return &storage;
    }

    void check() {
        if (storage)
            throw gexception(storage);
    }
};

}
