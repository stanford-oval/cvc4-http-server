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
#include <string>
#include <cassert>

#include <cvc4/cvc4.h>
#include <cvc4/options/set_language.h>

#include "solver.hpp"

using namespace std::literals;

namespace cvc4_http
{

std::mutex Solver::option_lock;

Solver::Solver()
    : options(const_cast<CVC4::Options&>(expr_manager.getOptions()))
{
    static const char * const opt_strings[] = {
        "cvc4-http-server",
        "--dump-models"
    };

    std::lock_guard<std::mutex> guard(option_lock);
    CVC4::Options::parseOptions(&options, sizeof(opt_strings)/sizeof(opt_strings[0]), (char**)opt_strings);
}

void Solver::process (std::istream & istream, std::ostream & ostream)
{
    CVC4::SmtEngine engine(&expr_manager);
    options.setOutputLanguage(CVC4::language::output::LANG_SMTLIB_V2_6);
    std::cerr << CVC4::language::SetLanguage(CVC4::language::output::LANG_CVC4);

    CVC4::parser::ParserBuilder parser_builder(&expr_manager, "<http>"s, options);
    parser_builder
        .withInputLanguage(CVC4::language::input::LANG_SMTLIB_V2)
        .withIncludeFile(false)
        .withStreamInput(istream);

    std::unique_ptr<CVC4::parser::Parser> parser(parser_builder.build());

    while (!parser->done()) {
        std::unique_ptr<CVC4::Command> command(parser->nextCommand());
        if (command == nullptr)
            continue;
        std::cerr << "Command: " << *command << std::endl;
        command->invoke(&engine, ostream);
        maybe_dump_models (engine, command, ostream);
    }
}

void Solver::maybe_dump_models(CVC4::SmtEngine& engine, const std::unique_ptr<CVC4::Command>& command, std::ostream & ostream)
{
    CVC4::Result res;
    CVC4::CheckSatCommand* cs = dynamic_cast<CVC4::CheckSatCommand*>(command.get());
    if(cs != NULL)
        res = cs->getResult();
    CVC4::QueryCommand* q = dynamic_cast<CVC4::QueryCommand*>(command.get());
    if(q != NULL)
        res = q->getResult();
    if (res.isNull())
        return;

    std::unique_ptr<CVC4::Command> c;
    if (res.asSatisfiabilityResult() == CVC4::Result::SAT ||
        (res.isUnknown() && res.whyUnknown() == CVC4::Result::INCOMPLETE)) {
        c.reset(new CVC4::GetModelCommand());
    }
    if (c)
        c->invoke(&engine, ostream);
}

}
