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
#include <future>
#include <list>
#include <vector>
#include <thread>

#include <glib.h>

#include "refptr.hpp"
#include "gexcept.hpp"

namespace cvc4_http {

inline void free_thread_pool(GThreadPool* pool) {
    g_thread_pool_free(pool, false, true);
}

template<class Scope>
class threadpool {
private:
    template<class V>
    class async_queue {
    private:
        std::list<V> list;
        std::condition_variable cond;
        std::mutex lock;

    public:
        void push(V&& v) {
            std::lock_guard<std::mutex> guard(lock);
            list.push_back(std::move(v));
            cond.notify_one();
        }

        template<class ...Args>
        void emplace(Args&&... args) {
            std::lock_guard<std::mutex> guard(lock);
            list.emplace_back(std::forward<Args>(args)...);
            cond.notify_one();
        }

        V pop() {
            std::unique_lock<std::mutex> ulock(lock);
            while (list.empty())
                cond.wait(ulock);
            V v = list.front();
            list.pop_front();
            return v;
        }
    };

    async_queue<std::function<void(Scope&)>> queue;
    std::vector<std::thread> threads;
    void thread_func() {
        Scope scope;

        while (true) {
            std::function<void(Scope&)> call = queue.pop();
            if (call == nullptr)
                return;
            call(scope);
        }
    }

    void init(int max_threads) {
        threads.reserve(max_threads);

        for (int i = 0; i < max_threads; i++) {
            threads.emplace_back(std::bind(&threadpool::thread_func, this));
        }
    }

public:
    threadpool(int max_threads) {
        init(max_threads);
    }

    ~threadpool() {
        for (size_t i = 0; i < threads.size(); i++) {
            queue.emplace(nullptr);
            threads[i].join();
        }
    }

    template<class Callable>
    void push(Callable&& task) {
        queue.emplace(std::forward<Callable>(task));
    }
};

}
