// By Manuel Simoni <msimoni@gmail.com>, August 2011
// In the public domain.

// An interpreter with tail-call elimination and multi-shot
// continuations modelled after Kent Dybvig's dissertation
// ``Three Implementation Models for Scheme'', section 3.4.
// http://www.cs.indiana.edu/~dyb/pubs/3imp.pdf
//
// Examples:
// ["set!", "x", 1]
// "x" --> 1
//
// ["call/cc", ["lambda", ["k"], ["k", 12]]] --> 12
//
// Differences:
// - Arguments are evaluated left-to-right instead of right-to-left.

/**** Virtual Machine ****/

function Scm_vm()
{
    // Accumulator
    this.a = null;
    // neXt instruction
    this.x = null;
    // Environment
    this.e = scm_make_env();
    // aRguments
    this.r = scm_make_args();
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
        case "quote":
            var obj = scm_compound_elt(form, 1);
            return { op: "constant", obj: obj, next: next };
        case "lambda":
            var vars = scm_compound_elt(form, 1);
            var body = scm_compound_elt(form, 2);
            return { op: "close",
                     vars: vars,
                     body: scm_compile(body, { op: "return" }),
                     next: next };
        case "if":
            var test = scm_compound_elt(form, 1);
            var consequent = scm_compound_elt(form, 2);
            var alternative = scm_compound_elt(form, 3);
            var consequent_insn = scm_compile(consequent, next);
            var alternative_insn = scm_compile(alternative, next);
            return scm_compile(test, { op: "test",
                                       consequent: consequent_insn,
                                       alternative: alternative_insn });
        case "set!":
            var name = scm_compound_elt(form, 1);
            var value = scm_compound_elt(form, 2);
            return scm_compile(value, { op: "assign", name: name, next: next });
        case "call/cc":
            return scm_compile_callcc(form, next);
        default:
            return scm_compile_application(form, next);
        }
    } else {
        return { op: "constant", obj: form, next: next };
    }
}

function scm_compile_callcc(form, next)
{
    var f = scm_compound_elt(form, 1);
    var c = { op: "conti",
              next: { op: "argument",
                      next: scm_compile(f, { op: "apply" }) } };
    if (scm_is_return(next)) {
        return c;
    } else {
        return { op: "frame", ret: next, next: c };
    }
}

function scm_compile_application(form, next)
{
    var f = scm_compound_elt(form, 0);
    return compile_application(scm_compile(f, { op: "apply" }), 1);

    function compile_application(c, i)
    {
        if (i === scm_compound_length(form)) {
            if (scm_is_return(next)) {
                return c;
            } else {
                return { op: "frame", ret: next, next: c };
            }
        } else {
            return compile_application(scm_compile(scm_compound_elt(form, i),
                                                   { op: "argument", next: c }),
                                       i + 1);
        }
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
            vm.a = scm_make_closure(insn.body, vm.e, insn.vars);
            vm.x = insn.next;
            continue;
        case "test":
            vm.x = vm.a ? insn.consequent : insn.alternative;
            continue;
        case "assign":
            scm_update(vm.e, insn.name, vm.a);
            vm.x = insn.next;
            continue;
        case "conti":
            vm.a = scm_make_continuation(vm.s);
            vm.x = insn.next;
            continue;
        case "nuate":
            vm.a = scm_lookup(vm.e, insn.name);
            vm.x = { op: "return" };
            vm.s = insn.s;
            continue;
        case "frame":
            vm.x = insn.next;
            vm.r = scm_make_args();
            vm.s = scm_make_frame(insn.ret, vm.e, vm.r, vm.s);
            continue;
        case "argument":
            scm_push_arg(vm.r, vm.a);
            vm.x = insn.next;
            continue;
        case "apply":
            vm.x = vm.a.body;
            vm.e = scm_extend(vm.a.e, vm.a.vars, vm.r);
            vm.r = scm_make_args();
            continue;
        case "return":
            vm.x = vm.s.x;
            vm.e = vm.s.e;
            vm.r = vm.s.r;
            vm.s = vm.s.s;
            continue;
        }
    }
}

function scm_make_continuation(s)
{
    return scm_make_closure({ op: "nuate", name: "v", s: s },
                            scm_make_env(),
                            ["v"]);
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

function scm_extend(env, vars, args)
{
    var xenv = scm_make_env(env);
    for (var i = 0; (i < vars.length) && (i < args.length); i++) {
        scm_just_update(xenv, vars[i], args[i]);
    }
    return xenv;
}

/**** Closures, Call Frames, Arguments ****/

function Scm_closure(body, env, vars)
{
    this.body = body;
    this.env = env;
    this.vars = vars;
}

function scm_make_closure(body, env, args)
{
    return new Scm_closure(body, env, args);
}

function Scm_frame(x, e, r, s)
{
    this.x = x;
    this.e = e;
    this.r = r;
    this.s = s;
}

function scm_make_frame(x, e, r, s)
{
    return new Scm_frame(x, e, r, s);
}

function scm_make_args()
{
    return [];
}

function scm_push_arg(args, value)
{
    args.push(value);
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
