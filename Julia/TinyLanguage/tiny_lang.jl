# tiny_lang.jl — Julia port of tiny_lang (parser -> IR -> Julia codegen)
# Features: let, print, if/else, while, fn, return, call stmt, new/delete, tag, operator overloading,
# comparisons (> >= == <= <), arithmetic (+ - * /). Heap is 0-based (mapped to Julia's 1-based).
#
# Usage:
#   julia tiny_lang.jl demo.tiny --run
#   julia tiny_lang.jl demo.tiny --emit out.jl
#
# No external packages required.

############## Tracing (optional) ##############
const TRACE_LEX   = Ref(false)
const TRACE_PARSE = Ref(false)

############## Lexer ##############

struct Token
    kind::Symbol   # :NAME, :NUMBER, :OP, :SYMBOL, :KW, :EOF
    text::String
    pos::Int
end

mutable struct Lexer
    s::String
    i::Int
    n::Int
end

function Lexer(s::String)
    Lexer(s, firstindex(s), lastindex(s))
end

# identifier helpers (Julia: isletter/isdigit)
is_name_start(c::Char) = (c == '_') || isletter(c)
is_name_char(c::Char)  = (c == '_') || isletter(c) || isdigit(c)

const KEYWORDS = Set(["let","print","if","else","while","fn","delete","return","tag","operator","new"])

# trace helper
trace_lex_token(tok::Token) = (TRACE_LEX[] && @info "LEX" kind=tok.kind text=tok.text pos=tok.pos; tok)

function skip_ws_and_comments!(lx::Lexer)
    while lx.i <= lx.n
        c = lx.s[lx.i]
        if c == ' ' || c == '\t' || c == '\r' || c == '\n'
            lx.i = nextind(lx.s, lx.i); continue
        end
        # line comment //
        ni = (lx.i < lx.n) ? nextind(lx.s, lx.i) : lx.i
        if c == '/' && lx.i < lx.n && lx.s[ni] == '/'
            # skip until newline or end
            lx.i = ni
            while lx.i <= lx.n && lx.s[lx.i] != '\n'
                lx.i = nextind(lx.s, lx.i)
            end
            continue
        end
        break
    end
end

function next_token(lx::Lexer)
    skip_ws_and_comments!(lx)
    pos = lx.i
    if lx.i > lx.n
        return trace_lex_token(Token(:EOF, "", pos))
    end
    c = lx.s[lx.i]

    # names / keywords
    if is_name_start(c)
        j = nextind(lx.s, lx.i)
        while j <= lx.n && is_name_char(lx.s[j])
            j = nextind(lx.s, j)
        end
        txt = lx.s[lx.i:prevind(lx.s, j)]
        lx.i = j
        if txt in KEYWORDS
            return trace_lex_token(Token(:KW, txt, pos))
        else
            return trace_lex_token(Token(:NAME, txt, pos))
        end
    end

    # numbers (digits with optional dot)
    if isdigit(c)
        j = nextind(lx.s, lx.i)
        hasdot = false
        while j <= lx.n
            cj = lx.s[j]
            if cj == '.' && !hasdot
                hasdot = true
                j = nextind(lx.s, j)
            elseif isdigit(cj)
                j = nextind(lx.s, j)
            else
                break
            end
        end
        txt = lx.s[lx.i:prevind(lx.s, j)]
        lx.i = j
        return trace_lex_token(Token(:NUMBER, txt, pos))
    end

    # two-char operators: >= <= ==
    if (c == '>' || c == '<' || c == '=')
        j = (lx.i < lx.n) ? nextind(lx.s, lx.i) : lx.i
        if lx.i < lx.n && lx.s[j] == '='
            txt = string(c, '=')
            lx.i = nextind(lx.s, j)
            return trace_lex_token(Token(:OP, txt, pos))
        end
    end

    # single-char operators and symbols (include '=' as assignment)
    if c in ['+','-','*','/','>','<']
        lx.i = nextind(lx.s, lx.i)
        return trace_lex_token(Token(:OP, string(c), pos))
    end
    if c in ['(',')','{','}',';',',',':','=']
        lx.i = nextind(lx.s, lx.i)
        return trace_lex_token(Token(:SYMBOL, string(c), pos))
    end

    error("Lexing error at position $pos (char = '$(c)')")
end

############## AST / IR ##############

abstract type IR end
struct Let    <: IR; name::String; expr::IR; end
struct Print  <: IR; expr::IR; end
struct If     <: IR; cond::IR; then_::Vector{IR}; els::Vector{IR}; end
struct While  <: IR; cond::IR; body::Vector{IR}; end
struct Fn     <: IR; name::String; params::Vector{String}; body::Vector{IR}; end
struct CallStmt <: IR; name::String; args::Vector{IR}; end
struct Delete <: IR; ptr::IR; end
struct Return <: IR; expr::IR; end
struct TagStmt <: IR; varname::String; typename::String; end
struct OpDef  <: IR; op::String; a_name::String; a_type::String; b_name::String; b_type::String; ret_type::String; body::Vector{IR}; end

# exprs
struct Num  <: IR; v::Float64; end
struct Var  <: IR; name::String; end
struct Call <: IR; name::String; args::Vector{IR}; end
struct Bin  <: IR; op::String; a::IR; b::IR; end
struct New  <: IR; size::IR; end

############## Parser ##############

mutable struct Parser
    lx::Lexer
    look::Token
end

function Parser(s::String)
    lx = Lexer(s)
    tk = next_token(lx)
    Parser(lx, tk)
end

function advance!(p::Parser)
    p.look = next_token(p.lx)
end

function expect!(p::Parser, kind::Symbol, txt::Union{Nothing,String}=nothing)
    t = p.look
    TRACE_PARSE[] && @info "EXPECT" want_kind=kind want_txt=txt got_kind=t.kind got_txt=t.text pos=t.pos
    ok = (t.kind == kind) && (txt === nothing || t.text == txt)
    if !ok
        want = string(kind)
        wanttxt = txt === nothing ? "" : " " * txt
        got = string(t.kind, " '", t.text, "'")
        error("Parse error near pos $(t.pos): expected $(want)$(wanttxt) but got $(got)")
    end
    advance!(p)
    return t
end

function accept!(p::Parser, kind::Symbol, txt::Union{Nothing,String}=nothing)
    t = p.look
    if t.kind == kind && (txt === nothing || t.text == txt)
        advance!(p); return true
    end
    return false
end

# program := stmt*
function parse_program(p::Parser)
    stmts = IR[]
    while p.look.kind != :EOF
        push!(stmts, parse_stmt(p))
    end
    return stmts
end

function parse_block(p::Parser)
    expect!(p, :SYMBOL, "{")
    stmts = IR[]
    while !(p.look.kind == :SYMBOL && p.look.text == "}")
        push!(stmts, parse_stmt(p))
    end
    expect!(p, :SYMBOL, "}")
    return stmts
end

function parse_params(p::Parser)
    names = String[]
    if p.look.kind == :NAME
        push!(names, expect!(p, :NAME).text)
        while accept!(p, :SYMBOL, ",")
            push!(names, expect!(p, :NAME).text)
        end
    end
    return names
end

function parse_args(p::Parser)
    args = IR[]
    if !(p.look.kind == :SYMBOL && p.look.text == ")")
        push!(args, parse_expr(p))
        while accept!(p, :SYMBOL, ",")
            push!(args, parse_expr(p))
        end
    end
    return args
end

# stmt
function parse_stmt(p::Parser)::IR
    t = p.look
    if t.kind == :KW
        if t.text == "let"
            advance!(p)
            name = expect!(p, :NAME).text
            expect!(p, :SYMBOL, "=")
            expr = parse_expr(p)
            expect!(p, :SYMBOL, ";")
            return Let(name, expr)
        elseif t.text == "print"
            advance!(p); expect!(p, :SYMBOL, "(")
            e = parse_expr(p)
            expect!(p, :SYMBOL, ")"); expect!(p, :SYMBOL, ";")
            return Print(e)
        elseif t.text == "if"
            advance!(p); expect!(p, :SYMBOL, "(")
            c = parse_expr(p)
            expect!(p, :SYMBOL, ")")
            then_blk = parse_block(p)
            els_blk = IR[]
            if p.look.kind == :KW && p.look.text == "else"
                advance!(p)
                els_blk = parse_block(p)
            end
            return If(c, then_blk, els_blk)
        elseif t.text == "while"
            advance!(p); expect!(p, :SYMBOL, "(")
            c = parse_expr(p)
            expect!(p, :SYMBOL, ")")
            body = parse_block(p)
            return While(c, body)
        elseif t.text == "fn"
            advance!(p)
            fname = expect!(p, :NAME).text
            expect!(p, :SYMBOL, "(")
            params = parse_params(p)
            expect!(p, :SYMBOL, ")")
            body = parse_block(p)
            return Fn(fname, params, body)
        elseif t.text == "delete"
            advance!(p); expect!(p, :SYMBOL, "(")
            pe = parse_expr(p)
            expect!(p, :SYMBOL, ")"); expect!(p, :SYMBOL, ";")
            return Delete(pe)
        elseif t.text == "return"
            advance!(p)
            e = parse_expr(p)
            expect!(p, :SYMBOL, ";")
            return Return(e)
        elseif t.text == "tag"
            advance!(p); expect!(p, :SYMBOL, "(")
            vname = expect!(p, :NAME).text
            expect!(p, :SYMBOL, ",")
            tname = expect!(p, :NAME).text
            expect!(p, :SYMBOL, ")"); expect!(p, :SYMBOL, ";")
            return TagStmt(vname, tname)
        elseif t.text == "operator"
            advance!(p)
            op_t = expect!(p, :OP)  # + - * / > >= < <= ==
            op = op_t.text
            expect!(p, :SYMBOL, "(")
            a_name = expect!(p, :NAME).text
            expect!(p, :SYMBOL, ":")
            a_type = expect!(p, :NAME).text
            expect!(p, :SYMBOL, ",")
            b_name = expect!(p, :NAME).text
            expect!(p, :SYMBOL, ":")
            b_type = expect!(p, :NAME).text
            expect!(p, :SYMBOL, ")")
            # expect '->' as two tokens '-' and '>'
            expect!(p, :OP, "-")
            expect!(p, :OP, ">")
            ret_type = expect!(p, :NAME).text  # decorative
            body = parse_block(p)
            return OpDef(op, a_name, a_type, b_name, b_type, ret_type, body)
        end
    end
    # call_stmt: NAME "(" [args] ")" ";"
    if t.kind == :NAME
        name = t.text; advance!(p)
        expect!(p, :SYMBOL, "(")
        args = parse_args(p)
        expect!(p, :SYMBOL, ")"); expect!(p, :SYMBOL, ";")
        return CallStmt(name, args)
    end
    error("Parse error near pos $(t.pos): unexpected token $(t.kind) '$(t.text)'")
end

# expressions
function parse_expr(p::Parser)
    parse_equality(p)
end

function parse_equality(p::Parser)
    left = parse_comparison(p)
    while p.look.kind == :OP && p.look.text == "=="
        advance!(p)
        right = parse_comparison(p)
        left = Bin("==", left, right)
    end
    return left
end

function parse_comparison(p::Parser)
    left = parse_sum(p)
    while p.look.kind == :OP && (p.look.text in (">", ">=", "<", "<="))
        op = p.look.text; advance!(p)
        right = parse_sum(p)
        left = Bin(op, left, right)
    end
    return left
end

function parse_sum(p::Parser)
    left = parse_term(p)
    while p.look.kind == :OP && (p.look.text == "+" || p.look.text == "-")
        op = p.look.text; advance!(p)
        right = parse_term(p)
        left = Bin(op, left, right)
    end
    return left
end

function parse_term(p::Parser)
    left = parse_factor(p)
    while p.look.kind == :OP && (p.look.text == "*" || p.look.text == "/")
        op = p.look.text; advance!(p)
        right = parse_factor(p)
        left = Bin(op, left, right)
    end
    return left
end

function parse_factor(p::Parser)
    t = p.look
    if t.kind == :KW && t.text == "new"
        advance!(p); expect!(p, :SYMBOL, "(")
        e = parse_expr(p)
        expect!(p, :SYMBOL, ")")
        return New(e)
    elseif t.kind == :NUMBER
        advance!(p)
        return Num(parse(Float64, t.text))
    elseif t.kind == :NAME
        name = t.text; advance!(p)
        if accept!(p, :SYMBOL, "(")
            args = parse_args(p)
            expect!(p, :SYMBOL, ")")
            return Call(name, args)
        else
            return Var(name)
        end
    elseif t.kind == :SYMBOL && t.text == "("
        advance!(p)
        e = parse_expr(p)
        expect!(p, :SYMBOL, ")")
        return e
    else
        error("Parse error near pos $(t.pos): unexpected token in expression $(t.kind) '$(t.text)'")
    end
end

############## Codegen ##############

mutable struct Emitter
    lines::Vector{String}
    ind::Int
end
Emitter() = Emitter(String[], 0)

# <- FIX: accept AbstractString so SubString works
function emit!(em::Emitter, s::AbstractString = "")
    push!(em.lines, repeat("    ", em.ind) * String(s))
end

function mangle_op(op::String)
    if op == "+"; return "add"
    elseif op == "-"; return "sub"
    elseif op == "*"; return "mul"
    elseif op == "/"; return "div"
    elseif op == "=="; return "eq"
    elseif op == ">"; return "gt"
    elseif op == ">="; return "ge"
    elseif op == "<"; return "lt"
    elseif op == "<="; return "le"
    else; error("unknown op $op")
    end
end

const RUNTIME_JL = """
# --- tiny runtime with overloading (Julia) ---
const __heap = Dict{Int, Vector{Any}}()
const __ptr_tags = Dict{Int, String}()
const __ops = Dict{Tuple{String, Union{Nothing,String}, Union{Nothing,String}}, Function}()
__next_ptr = Ref(1)

function __new(n)
    p = __next_ptr[]
    __next_ptr[] += 1
    __heap[p] = [0 for _ in 1:Int(n)]
    return p
end

function __delete(p)
    p = Int(p)
    pop!(__heap, p, nothing)
    pop!(__ptr_tags, p, nothing)
    return nothing
end

heap_get(p, i) = __heap[Int(p)][Int(i)+1]
function heap_set(p, i, v)
    __heap[Int(p)][Int(i)+1] = v
    return nothing
end

function __tag_ptr(p, tag)
    __ptr_tags[Int(p)] = String(tag)
    return nothing
end

function __get_tag(v)
    if v isa Dict && haskey(v, "__tag__")
        return v["__tag__"]
    end
    try
        iv = Int(v)
        if haskey(__ptr_tags, iv)
            return __ptr_tags[iv]
        end
    catch
    end
    return nothing
end

function __register_op(op, ta, tb, fn)
    __ops[(String(op), ta === nothing ? nothing : String(ta), tb === nothing ? nothing : String(tb))] = fn
    return nothing
end

function __binop(op, a, b)
    ta = __get_tag(a); tb = __get_tag(b)
    key = (String(op), ta, tb)
    if haskey(__ops, key)
        return __ops[key](a, b)
    end
    op = String(op)
    if op == "+"; return a + b
    elseif op == "-"; return a - b
    elseif op == "*"; return a * b
    elseif op == "/"; return a / b
    elseif op == ">"; return a > b
    elseif op == ">="; return a >= b
    elseif op == "<"; return a < b
    elseif op == "<="; return a <= b
    elseif op == "=="; return a == b
    else
        error("unsupported op " * op)
    end
end

box(v) = Dict("__tag__"=>"Box", "v"=>v)
unbox(b) = b["v"]
"""

function gen_expr(em::Emitter, e::IR)::String
    if e isa Num
        return string((e::Num).v)
    elseif e isa Var
        return (e::Var).name
    elseif e isa Call
        ee = (e::Call)
        argstrs = [gen_expr(em, a) for a in ee.args]
        return string(ee.name, "(", join(argstrs, ", "), ")")
    elseif e isa New
        return string("__new(", gen_expr(em, (e::New).size), ")")
    elseif e isa Bin
        ee = (e::Bin)
        return string("__binop(\"", ee.op, "\", ", gen_expr(em, ee.a), ", ", gen_expr(em, ee.b), ")")
    else
        error("unknown expr node")
    end
end

function gen_stmt!(em::Emitter, s::IR)
    if s isa Let
        emit!(em, string((s::Let).name, " = ", gen_expr(em, (s::Let).expr)))
    elseif s isa Print
        emit!(em, string("println(", gen_expr(em, (s::Print).expr), ")"))
    elseif s isa If
        ss = (s::If)
        emit!(em, string("if ", gen_expr(em, ss.cond)))
        em.ind += 1
        for st in ss.then_; gen_stmt!(em, st); end
        em.ind -= 1
        if !isempty(ss.els)
            emit!(em, "else")
            em.ind += 1
            for st in ss.els; gen_stmt!(em, st); end
            em.ind -= 1
        end
        emit!(em, "end")
    elseif s isa While
        ss = (s::While)
        emit!(em, string("while ", gen_expr(em, ss.cond)))
        em.ind += 1
        for st in ss.body; gen_stmt!(em, st); end
        em.ind -= 1
        emit!(em, "end")
    elseif s isa Fn
        ss = (s::Fn)
        emit!(em, string("function ", ss.name, "(", join(ss.params, ", "), ")"))
        em.ind += 1
        if isempty(ss.body)
            emit!(em, "nothing")
        else
            for st in ss.body; gen_stmt!(em, st); end
        end
        em.ind -= 1
        emit!(em, "end")
    elseif s isa CallStmt
        ss = (s::CallStmt)
        argstrs = [gen_expr(em, a) for a in ss.args]
        emit!(em, string(ss.name, "(", join(argstrs, ", "), ")"))
    elseif s isa Delete
        emit!(em, string("__delete(", gen_expr(em, (s::Delete).ptr), ")"))
    elseif s isa Return
        emit!(em, string("return ", gen_expr(em, (s::Return).expr)))
    elseif s isa TagStmt
        ss = (s::TagStmt)
        emit!(em, string("__tag_ptr(", ss.varname, ", \"", ss.typename, "\")"))
    elseif s isa OpDef
        fname = string("__op_", mangle_op(s.op), "_", s.a_type, "_", s.b_type)
        emit!(em, "function $(fname)($(s.a_name), $(s.b_name))")
        em.ind += 1
        if isempty(s.body)
            emit!(em, "nothing")
        else
            for st in s.body; gen_stmt!(em, st); end
        end
        em.ind -= 1
        emit!(em, "end")
        emit!(em, "__register_op(\"$(s.op)\", \"$(s.a_type)\", \"$(s.b_type)\", $(fname))")
        emit!(em, "")
    else
        error("unknown stmt node")
    end
end

function gen_program(stmts::Vector{IR})::String
    em = Emitter()
    emit!(em, "# generated from tiny language (Julia port)")
    for ln in split(RUNTIME_JL, '\n'); emit!(em, ln); end
    emit!(em, "")
    # generate operator defs first
    for s in stmts
        if s isa OpDef; gen_stmt!(em, s); end
    end
    # then the rest
    for s in stmts
        if !(s isa OpDef); gen_stmt!(em, s); end
    end
    return join(em.lines, "\n")
end

############## Driver ##############

function compile_to_julia(src::String)::String
    p = Parser(src)
    ir = parse_program(p)
    return gen_program(ir)
end

if abspath(PROGRAM_FILE) == @__FILE__
    if length(ARGS) < 1
        println("Usage: julia tiny_lang.jl <source.tiny> [--emit out.jl] [--run] [--trace-lex] [--trace-parse]")
        exit(0)
    end

    # optional tracing flags
    if any(==("--trace-lex"), ARGS);   TRACE_LEX[] = true;   end
    if any(==("--trace-parse"), ARGS); TRACE_PARSE[] = true; end

    # ---- robust path resolving ----
    src_arg = ARGS[1]
    function resolve_src(arg::AbstractString)
        if isabspath(arg) && isfile(arg); return arg; end
        p1 = joinpath(@__DIR__, arg);                 if isfile(p1); return p1; end
        p2 = joinpath(@__DIR__, "TinyLanguage", arg); if isfile(p2); return p2; end
        p3 = joinpath(pwd(), arg);                    if isfile(p3); return p3; end
        error("Source file not found: $arg\n  @__DIR__=$(abspath(@__DIR__))\n  pwd()=$(abspath(pwd()))")
    end
    src_path = resolve_src(src_arg)

    src = read(src_path, String)

    code = try
        compile_to_julia(src)
    catch err
        showerror(stdout, err, catch_backtrace()); println()
        exit(1)
    end

    if any(==("--emit"), ARGS)
        idx = findfirst(==("--emit"), ARGS)
        outpath = (idx !== nothing && idx < length(ARGS)) ? ARGS[idx+1] : "out.jl"
        open(outpath, "w") do io; write(io, code); end
        println("Wrote ", outpath)
    end

    if any(==("--run"), ARGS)
        Base.include_string(Main, code, "generated.jl")
    elseif !any(==("--emit"), ARGS)
        println("Compilation successful. Use --emit out.jl to write the generated Julia, or --run to execute.")
    end
end
