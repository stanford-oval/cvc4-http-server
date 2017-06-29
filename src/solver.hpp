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
#include <iostream>
#include <mutex>

#include <cvc4/cvc4.h>

namespace cvc4_http {

class Solver {
private:
    static std::mutex option_lock;

    CVC4::ExprManager expr_manager;
    CVC4::Options& options;

    void maybe_dump_models(CVC4::SmtEngine&, const std::unique_ptr<CVC4::Command>& command, std::ostream &);

public:
    Solver();

    void process(std::istream&, std::ostream&);
};

}
