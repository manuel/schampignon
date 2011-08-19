// By Manuel Simoni <msimoni@gmail.com>, August 2011
// In the public domain.

// An interpreter for a very minimal, Kernel-like language:
//
// [["$vau", "x", "%ignore", "x"], 1, 2] --> [1, 2]

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

/**** Compilation ****/

function scm_compile(form, next)
{
    if (scm_is_symbol(form)) {
        return { op: "refer", name: form, next: next };
    } else if (scm_is_compound(form)) {
        switch(scm_compound_operator(form)) {
        case "$vau":
            var sig = scm_compound_elt(form, 1);
            var denv = scm_compound_elt(form, 2);
            var body = scm_compound_elt(form, 3);
            return { op: "close",
                     sig: sig,
                     denv: denv,
                     body: scm_compile(body, { op: "return" }),
                     next: next };
        case "$define!":
            var name = scm_compound_elt(form, 1);
            var value = scm_compound_elt(form, 2);
            return scm_compile(value, { op: "assign", name: name, next: next });
        default:
            return scm_compile_application(form, next);
        }
    } else {
        return { op: "constant", obj: form, next: next };
    }
}

function scm_compile_application(form, next)
{
    var f = scm_compound_elt(form, 0);
    /* Difference to Scheme interpreter:
       We simply store the rest of the form in the apply instruction. */
    var c = scm_compile(f, { op: "apply", form: form.slice(1) });
    if (scm_is_return(next)) {
        return c;
    } else {
        return { op: "frame", ret: next, next: c };
    }
}

function scm_is_return(insn)
{
    return insn.op === "return";
}

/**** Evaluation ****/

function scm_eval(vm, form)
{
    vm.x = scm_compile(form, { op: "halt" });
    while(true) {
        var insn = vm.x;
        switch(insn.op) {
        case "halt":
            return vm.a;
        case "refer":
            vm.a = scm_lookup(vm.e, insn.name);
            vm.x = insn.next;
            continue;
        case "constant":
            vm.a = insn.obj;
            vm.x = insn.next;
            continue;
        case "close":
            vm.a = scm_make_closure(insn.body, vm.e, insn.sig, insn.denv);
            vm.x = insn.next;
            continue;
        case "assign":
            scm_update(vm.e, insn.name, vm.a);
            vm.x = insn.next;
            continue;
        case "frame":
            vm.x = insn.next;
            vm.s = scm_make_frame(insn.ret, vm.e, vm.s);
            continue;
        case "apply":
            vm.x = vm.a.body;
            vm.e = scm_extend(vm.a.e, vm.a.sig, vm.a.denv, insn.form);
            continue;
        case "return":
            vm.x = vm.s.x;
            vm.e = vm.s.e;
            vm.s = vm.s.s;
            continue;
        }
    }
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
    /* Difference to Scheme interpreter:

       We just slap the form and the dynamic environment into the
       closure's extended environment.  (The form should really be
       destructured according to the signature.). */
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
