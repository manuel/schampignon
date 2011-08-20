// By Manuel Simoni <msimoni@gmail.com>, August 2011
// In the public domain.

// An interpreter for a very minimal, Kernel-like language:
//
// [["$vau", "x", "%ignore", "x"], 1, 2] --> [1, 2]
//
// ["$define!", "foo", ["$vau", "x", "%ignore", "x"]]
// ["foo", 1, 2, 3]
// --> [1, 2, 3]
//
// ["$define!", "bar", ["$vau", "x", "%ignore", ["foo", "x"]]]
// ["bar", 44]
// --> "x"
// (remember, these are fexprs ;))

/**** Virtual Machine ****/

function Scm_vm()
{
    // Accumulator
    this.a = null;
    // neXt state
    this.x = null;
    // Environment
    this.e = scm_make_env();
    // Stack
    this.s = null;
}

/**** Evaluation ****/

function scm_eval(vm, form)
{
    scm_interp(vm, form, scm_halt_state, false);
    while(vm.x(vm));
    return vm.a;
}

function scm_interp(vm, form, next, tail)
{
    if (scm_is_symbol(form)) {
        vm.a = scm_lookup(vm.e, form);
        vm.x = next;
    } else if (scm_is_compound(form)) {
        switch (scm_compound_operator(form)) {
        case "$vau":
            var sig = scm_compound_elt(form, 1);
            var denv = scm_compound_elt(form, 2);
            var body = scm_compound_elt(form, 3);
            vm.a = scm_make_closure(body, vm.e, sig, denv);
            vm.x = next;
            break;
        case "$define!":
            var name = scm_compound_elt(form, 1);
            var value = scm_compound_elt(form, 2);
            scm_interp(vm, value, scm_assign_state(name, next), false);
            break;
        default:
            var combiner = scm_compound_elt(form, 0);
            var operands = scm_compound_slice(form, 1);
            scm_interp(vm, combiner, scm_combine_state(operands, next, tail), false);
        }
    } else {
        vm.a = form;
        vm.x = next;
    }
}

function scm_assign_state(name, next)
{
    return function(vm) {
        scm_update(vm.e, name, vm.a);
        vm.x = next;
        return true;
    };
}

function scm_combine_state(operands, next, tail)
{
    return function(vm) {
        var closure = vm.a;
        if (!tail) {
            vm.s = scm_make_frame(next, vm.e, vm.s);
        }
        vm.e = scm_extend(closure.e, closure.sig, closure.denv, operands);
        scm_interp(vm, closure.body, tail ? next : scm_pop_state, true);
        return true;
    };
}

function scm_pop_state(vm)
{
    vm.x = vm.s.x;
    vm.e = vm.s.e;
    vm.s = vm.s.s;
}

function scm_halt_state(vm)
{
    return false;
}

/**** Environments ****/

function Scm_env(parent)
{
    this.parent = parent;
    this.bindings = {};
}

function scm_make_env(parent)
{
    return new Scm_env(parent);
}

function scm_lookup(env, name)
{
    var value = env.bindings[name];
    if (value !== undefined) {
        return value;
    } else {
        if (env.parent)
            return scm_lookup(env.parent, name);
        else
            scm_error("undefined variable");
    }
}

function scm_update(env, name, value)
{
    if (env.bindings[name] !== undefined) {
        scm_just_update(env, name, value);
    } else {
        if (env.parent)
            scm_update(env.parent, name, value);
        else
            scm_just_update(env, name, value);
    }
}

function scm_just_update(env, name, value)
{
    env.bindings[name] = value;
}

function scm_extend(env, sig, denv, form)
{
    var xenv = scm_make_env(env);
    scm_just_update(xenv, sig, form);
    scm_just_update(xenv, denv, env);
    return xenv;
}

/**** Closures, Call Frames, Arguments ****/

function Scm_closure(body, env, sig, denv)
{
    this.body = body;
    this.e = env;
    this.sig = sig;
    this.denv = denv;
}

function scm_make_closure(body, env, sig, denv)
{
    return new Scm_closure(body, env, sig, denv);
}

function Scm_frame(x, e, s)
{
    this.x = x;
    this.e = e;
    this.s = s;
}

function scm_make_frame(x, e, s)
{
    return new Scm_frame(x, e, s);
}

/**** Forms ****/

function scm_is_symbol(x)
{
    return (typeof(x) === "string");
}

function scm_is_compound(x)
{
    return (x instanceof Array);
}

function scm_compound_operator(x)
{
    scm_assert(scm_is_compound(x));
    return x[0];
}

function scm_compound_elt(x, i)
{
    scm_assert(scm_is_compound(x));
    return x[i];
}

function scm_compound_slice(x, i)
{
    scm_assert(scm_is_compound(x));
    return x.slice(i);
}

function scm_compound_length(x)
{
    scm_assert(scm_is_compound(x));
    return x.length;
}

/**** Utilities ****/

function scm_assert(b)
{
    if (!b) scm_error("assertion failed");
}

function scm_error(msg)
{
    throw msg;
}
