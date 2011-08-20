// An interpreter for a Kernel-like language.
// By Manuel Simoni <msimoni@gmail.com>, August 2011
// In the public domain.

/**** Virtual Machine ****/

function Scm_vm()
{
    // Accumulator
    this.a = null;
    // neXt instruction
    this.x = null;
    // Environment
    this.e = scm_make_env();
    // Stack
    this.s = null;
}

/**** Evaluation ****/

function scm_eval(vm, form)
{
    scm_compile(vm, form, scm_insn_halt, false);
    while(vm.x(vm));
    return vm.a;
}

function scm_compile(vm, form, next, tail)
{
    if (scm_is_symbol(form)) {
        vm.a = scm_lookup(vm.e, form);
        vm.x = next;
    } else if (scm_is_compound(form)) {
        switch (scm_compound_operator(form)) {
        case "$vau":
            var ptree = scm_compound_elt(form, 1);
            var eformal = scm_compound_elt(form, 2);
            var body = scm_compound_elt(form, 3);
            vm.a = scm_make_combiner(vm.e, ptree, eformal, body);
            vm.x = next;
            break;
        case "$define!":
            var ptree = scm_compound_elt(form, 1);
            var expr = scm_compound_elt(form, 2);
            scm_compile(vm, expr, scm_insn_define(ptree, next), false);
            break;
        default:
            var combiner = scm_compound_elt(form, 0);
            scm_compile(vm, combiner, scm_insn_combine(form, next, tail), false);
        }
    } else {
        vm.a = form;
        vm.x = next;
    }
}

function scm_insn_define(ptree, next)
{
    return function(vm) {
        scm_update(vm.e, ptree, vm.a);
        vm.x = next;
        return true;
    };
}

function scm_insn_combine(whole_form, next, tail)
{
    return function(vm) {
        if (!tail) vm.s = scm_make_frame(next, vm.e, vm.s);
        vm.e = scm_extend(vm.e, vm.a, whole_form);
        scm_compile(vm, vm.a.body, tail ? next : scm_insn_return, true);
        return true;
    };
}

function scm_insn_return(vm)
{
    vm.x = vm.s.x;
    vm.e = vm.s.e;
    vm.s = vm.s.s;
    return true;
}

function scm_insn_halt(vm)
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
    var value = scm_just_lookup(env, name);
    if (value !== undefined) {
        return value;
    } else {
        if (env.parent)
            return scm_lookup(env.parent, name);
        else
            scm_error("undefined variable");
    }
}

function scm_just_lookup(env, name)
{
    return env.bindings[name];
}

function scm_update(env, name, value)
{
    if (scm_just_lookup(env, name) !== undefined) {
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

function scm_extend(denv, combiner, whole_form)
{
    var xenv = scm_make_env(combiner.env);
    scm_just_update(xenv, combiner.ptree, whole_form.slice(1));
    scm_just_update(xenv, combiner.eformal, denv);
    return xenv;
}

/**** Combiners, Frames, Arguments ****/

function Scm_combiner(env, ptree, eformal, body)
{
    this.env = env;
    this.ptree = ptree;
    this.eformal = eformal;
    this.body = body;
}

function scm_make_combiner(env, ptree, eformal, body)
{
    return new Scm_combiner(env, ptree, eformal, body);
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

/**** Wrappers ****/

function Scm_wrapper(combiner)
{
    this.combiner = combiner;
}

function scm_wrap(combiner)
{
    return new Scm_wrapper(combiner);
}

function scm_unwrap(applicative)
{
    scm_assert(scm_is_applicative(combiner));
    return applicative.combiner;
}

function scm_is_applicative(combiner)
{
    return (combiner instanceof Scm_wrapper);
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
