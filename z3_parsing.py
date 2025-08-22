import ast

import z3

from question import Question, VariableType


def z3_parse(
    expr: ast.expr | ast.stmt, question: Question, ctx: z3.Context | None = None
):
    if isinstance(expr, ast.BinOp):
        return parse_binop(expr, question, ctx)
    elif isinstance(expr, ast.Constant):
        return parse_constant(expr, question, ctx)
    elif isinstance(expr, ast.Name):
        return parse_name(expr, question, ctx)
    elif isinstance(expr, ast.Expr):
        return z3_parse(expr.value, question, ctx)
    elif isinstance(expr, ast.Call):
        return parse_call(expr, question, ctx)
    elif isinstance(expr, ast.IfExp):
        return parse_if(expr, question, ctx)
    elif isinstance(expr, ast.Compare):
        return parse_compare(expr, question, ctx)
    elif isinstance(expr, ast.BoolOp):
        return parse_bool_op(expr, question, ctx)
    elif isinstance(expr, ast.UnaryOp):
        return parse_unary_op(expr, question, ctx)
    else:
        raise NotImplementedError(f'Unsupported expr: {ast.dump(expr, indent=2)}')


def parse_unary_op(
    expr: ast.UnaryOp, question: Question, ctx: z3.Context | None = None
):
    if isinstance(expr.op, ast.USub):
        inner_exp = z3_parse(expr.operand, question, ctx)
        return -inner_exp
    elif isinstance(expr.op, ast.Not):
        return z3.Not(z3_parse(expr.operand, question, ctx))
    else:
        raise NotImplementedError(f'Unsupported op: {type(expr.op)}')


def parse_bool_op(expr: ast.BoolOp, question: Question, ctx: z3.Context | None = None):
    values = [z3_parse(v, question, ctx) for v in expr.values]

    if isinstance(expr.op, ast.And):
        return z3.And(*values)
    elif isinstance(expr.op, ast.Or):
        return z3.Or(*values)
    else:
        raise NotImplementedError(f'Unsupported op: {type(expr.op)}')


def parse_constant(
    expr: ast.Constant, question: Question, ctx: z3.Context | None = None
):
    val = expr.value
    if isinstance(val, int):
        return z3.IntVal(val, ctx)
    elif isinstance(val, float):
        return z3.RealVal(val, ctx)
    elif isinstance(val, str):
        return z3.StringVal(val, ctx)
    if isinstance(val, bool):
        return z3.BoolVal(val, ctx)
    else:
        raise NotImplementedError(f'Unsupported expr: {type(val)}')


def parse_if(expr: ast.IfExp, question: Question, ctx: z3.Context | None = None):
    cond = z3_parse(expr.test, question, ctx)
    then_b = z3_parse(expr.body, question, ctx)
    else_b = z3_parse(expr.orelse, question, ctx)
    return z3.If(cond, then_b, else_b)


def parse_compare(expr: ast.Compare, question: Question, ctx: z3.Context | None = None):
    left = z3_parse(expr.left, question, ctx)

    if len(expr.ops) == 1 and isinstance(expr.ops[0], ast.In | ast.NotIn):
        right_node = expr.comparators[0]
        if not isinstance(right_node, ast.List | ast.Tuple | ast.Set):
            raise NotImplementedError('Right side must be one of: list, tuple, set')
        options = [z3_parse(e, question, ctx) for e in right_node.elts]
        return (
            z3.Or(*[left == o for o in options])
            if isinstance(expr.ops[0], ast.In)
            else z3.And(*[left != o for o in options])
        )

    rights = [z3_parse(c, question, ctx) for c in expr.comparators]

    def one(l, op, r):
        match op:
            case ast.Eq():
                return l == r
            case ast.NotEq():
                return l != r
            case ast.Lt():
                return l < r
            case ast.LtE():
                return l <= r
            case ast.Gt():
                return l > r
            case ast.GtE():
                return l >= r
            case ast.IsNot():
                return l != r
            case _:
                raise NotImplementedError(f'Unsupported compare op: {type(op)}')

    if len(expr.ops) == 1:
        return one(left, expr.ops[0], rights[0])

    clauses = []
    cur = left
    for op, r in zip(expr.ops, rights, strict=True):
        clauses.append(one(cur, op, r))
        cur = r
    return z3.And(*clauses)


def parse_call(expr: ast.Call, question: Question, ctx: z3.Context | None = None):  #
    assert isinstance(expr.func, ast.Name)
    call_name = expr.func.id.lower()

    arg = expr.args[0]

    def as_int(a):
        a = z3_parse(a, question, ctx)
        if isinstance(a, z3.ArithRef) and a.is_real():
            return z3.ToInt(a)
        return a

    match call_name:
        case 'is_int':
            ... # Reals only
            return z3.BoolVal(True, ctx)
            # assert len(expr.args) == 1
            # x = z3_parse(arg, question, ctx)
            # if isinstance(x, z3.ArithRef):
            #     return z3.BoolVal(True, ctx) if x.is_int() else (z3.ToInt(x) == x)
            # raise TypeError('is_int not arithmetic')
        case 'divides':
            ... # Reals only
            return z3.BoolVal(True, ctx)
            # assert len(expr.args) == 2
            # d = as_int(expr.args[0])
            # n = as_int(expr.args[1])
            # return n % d == 0
        case 'int':
            assert len(expr.args) == 1
            parsed_arg = z3_parse(arg, question, ctx)
            ... # REALS ONLY 
            return parsed_arg
            # if isinstance(parsed_arg, int):
            #     return z3.IntVal(parsed_arg, ctx)
            # elif isinstance(parsed_arg, z3.ArithRef):
            #     if parsed_arg.is_real():
            #         return z3.ToInt(parsed_arg)
            #     elif parsed_arg.is_int():
            #         return parsed_arg
            #     else:
            #         raise TypeError(f'Unexpected Z3 sort: {parsed_arg.sort()}')
            # else:
            #     raise AssertionError()
        case 'fraction':
            if len(expr.args) == 2:
                numerator = z3_parse(expr.args[0], question, ctx)
                denominator = z3_parse(expr.args[1], question, ctx)
                return numerator / denominator
            elif len(expr.args) == 1:
                return z3_parse(expr.args[0], question, ctx)
        case 'round':
            ... # REALS ONLY
            return z3_parse(arg, question, ctx)
            # assert len(expr.args) == 1
            # x = z3_parse(arg, question, ctx)
            # return z3.If(x - z3.ToInt(x) >= 0.5, z3.ToInt(x) + 1, z3.ToInt(x))
        case 'max':
            parsed_args = [z3_parse(arg, question, ctx) for arg in expr.args]
            if len(parsed_args) == 1:
                return parsed_args[0]
            elif len(parsed_args) == 2:
                return z3.If(
                    parsed_args[0] >= parsed_args[1], parsed_args[0], parsed_args[1]
                )
            else:
                result = parsed_args[0]
                for arg in parsed_args[1:]:
                    result = z3.If(result >= arg, result, arg)
                return result
        case 'min':
            parsed_args = [z3_parse(arg, question, ctx) for arg in expr.args]
            if len(parsed_args) == 1:
                return parsed_args[0]
            elif len(parsed_args) == 2:
                return z3.If(
                    parsed_args[0] <= parsed_args[1], parsed_args[0], parsed_args[1]
                )
            else:
                result = parsed_args[0]
                for arg in parsed_args[1:]:
                    result = z3.If(result <= arg, result, arg)
                return result

    raise NotImplementedError(f'Unsupported callee: {call_name}')


def parse_binop(expr: ast.BinOp, question: Question, ctx: z3.Context | None = None):
    left = z3_parse(expr.left, question, ctx)
    right = z3_parse(expr.right, question, ctx)

    assert isinstance(left, z3.ArithRef)
    assert isinstance(right, z3.ArithRef)

    match expr.op:
        case ast.Add():
            return left + right
        case ast.Sub():
            return left - right
        case ast.Mult():
            return left * right
        case ast.Div() | ast.FloorDiv():
            return left / right
        case ast.Mod():
            ... # REALS ONLY 
            # A way of saying 'ignore'
            return z3.BoolVal(True, ctx=ctx)
            # return left % right
            # def _to_int_if_real(t):
            #     if isinstance(t, z3.ArithRef) and t.is_real():
            #         return z3.ToInt(t)
            #     return t
            # return _to_int_if_real(left) % _to_int_if_real(right)
        case ast.Pow():
            return left**right
        case _:
            raise NotImplementedError(f'Unsupported operator: {type(expr.op)}')


def parse_name(expr: ast.Name, question: Question, ctx: z3.Context | None = None):
    if not isinstance(expr.ctx, ast.Load):
        raise AssertionError()

    name = expr.id
    init_variable_type = question.variable_types[name]
    return z3_var_from(name=name, orig_type=init_variable_type, ctx=ctx)


def z3_var_from(
    name: str, orig_type: VariableType, ctx: z3.Context | None = None
) -> z3.ArithRef | z3.SeqRef:
    match orig_type:
        case VariableType.FLOAT:
            return z3.Real(name=name, ctx=ctx)
        case VariableType.INT:
            ... # REALS ONLY 
            return z3.Real(name=name, ctx=ctx)
            # return z3.Int(name=name, ctx=ctx)
        case VariableType.STR:
            return z3.String(name=name, ctx=ctx)
    raise NotImplementedError(f'Unhandled type: {orig_type}')


def parse_public_constraint(constraint_str: str, question: Question, ctx: z3.Context):
    node = ast.parse(constraint_str).body
    assert len(node) == 1, 'Unhandled module len > 1'
    return z3_parse(node[0], question, ctx)


def parse_private_constraint(constraint_str: str, question: Question, ctx: z3.Context):
    node = ast.parse(constraint_str).body
    assert len(node) == 1, 'Unhandled module len > 1'
    return z3_parse(node[0], question, ctx)
