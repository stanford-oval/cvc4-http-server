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
#include <glib-object.h>

namespace cvc4_http {

template<class Obj>
struct gobject_copy_ops {
    static void ref(Obj *obj) {
        g_object_ref(obj);
    }
    static void unref(Obj *obj) {
        g_object_unref(obj);
    }
};

template<class Obj, class CopyOps = gobject_copy_ops<Obj>>
class gref_ptr {
private:
    Obj *obj;

public:
    gref_ptr() noexcept {
        obj = nullptr;
    }
    gref_ptr(Obj *obj_, bool adopt = true) noexcept : obj(obj_) {
        if (obj == nullptr)
            return;
        if (!adopt)
            CopyOps::ref(obj);
    }
    ~gref_ptr() {
        if (obj != nullptr)
            CopyOps::unref(obj);
    }
    gref_ptr(gref_ptr<Obj>&& o) noexcept {
        obj = o.obj;
        o.obj = nullptr;
    }
    gref_ptr(const gref_ptr<Obj>& o) noexcept {
        obj = o.obj;
        if (obj != nullptr)
            CopyOps::ref(obj);
    }

    Obj* get() const noexcept {
        return obj;
    }
    Obj* operator->() const noexcept {
        return obj;
    }

    explicit operator bool() const  noexcept {
        return obj != nullptr;
    }

    void clear() noexcept {
        if (obj != nullptr)
            CopyOps::unref(obj);
        obj = nullptr;
    }

    gref_ptr<Obj>& operator=(const gref_ptr<Obj>& o) noexcept {
        clear();
        obj = o.obj;
        if (obj != nullptr)
            CopyOps::ref(obj);
        return *this;
    }
    gref_ptr<Obj>& operator=(gref_ptr<Obj>&& o) noexcept {
        clear();
        obj = o.obj;
        o.obj = nullptr;
        return *this;
    }
};

template<class Obj>
inline gref_ptr<Obj> make_gref_ptr(Obj *obj, bool adopt = true)
{
    return gref_ptr<Obj>(obj, adopt);
}

template<class Obj, GType (*get_type)()>
class gboxed_ptr {
private:
    Obj *obj;

public:
    gboxed_ptr() noexcept {
        obj = nullptr;
    }
    gboxed_ptr(Obj *obj_, bool adopt = true) noexcept {
        if (obj_ == nullptr) {
            obj = obj_;
            return;
        }
        if (adopt) {
            obj = obj_;
        } else {
            obj = static_cast<Obj*>(g_boxed_copy(get_type(), obj_));
        }
    }
    ~gboxed_ptr() {
        if (obj != nullptr)
            g_boxed_free(get_type(), obj);
    }
    gboxed_ptr(gboxed_ptr<Obj, get_type>&& o) noexcept {
        obj = o.obj;
        o.obj = nullptr;
    }
    gboxed_ptr(const gboxed_ptr<Obj, get_type>& o) noexcept {
        if (o.obj == nullptr)
            obj = nullptr;
        else
            obj = static_cast<Obj*>(g_boxed_copy(get_type(), o.obj));
    }

    Obj* get() const noexcept {
        return obj;
    }
    Obj* operator->() const noexcept {
        return obj;
    }

    explicit operator bool() const  noexcept {
        return obj != nullptr;
    }

    void clear() noexcept {
        if (obj != nullptr)
            g_boxed_free(get_type(), obj);
        obj = nullptr;
    }

    gboxed_ptr<Obj, get_type>& operator=(const gboxed_ptr<Obj, get_type>& o) noexcept {
        clear();
        if (o.obj == nullptr)
            obj = nullptr;
        else
            obj = static_cast<Obj*>(g_boxed_copy(get_type(), o.obj));
        return *this;
    }
    gboxed_ptr<Obj, get_type>& operator=(gboxed_ptr<Obj, get_type>&& o) noexcept {
        clear();
        obj = o.obj;
        o.obj = nullptr;
        return *this;
    }
};

template<class Obj, void (*deleter)(Obj *)>
struct cstyle_deleter {
    void operator()(Obj *obj) const {
        deleter(obj);
    }
};

}
