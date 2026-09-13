"""GPL-2.0-or-later. Strict Clang-AST semantics for the supported C++ subset."""
from dataclasses import dataclass, field
import copy
import z3

F64 = z3.Float64()
RNE = z3.RNE()
ZERO = z3.FPVal(0, F64)

class Unsupported(ValueError):
    pass

@dataclass(frozen=True)
class Pointer:
    region: str
    offset: int = 0

    def add(self, count):
        if not isinstance(count, int):
            raise Unsupported("Symbolic pointer arithmetic")
        return Pointer(self.region, self.offset + count)

@dataclass
class Memory:
    cells: dict = field(default_factory=dict)
    readonly: set = field(default_factory=set)
    access_log: list = field(default_factory=list)

    def access(self, ptr, kind, writing=False):
        if not isinstance(ptr, Pointer) or kind not in {"f64", "i32"}:
            raise Unsupported("Non-affine pointer or unsupported memory type")
        width = 8 if kind == "f64" else 4
        low, high = (-512, 0) if ptr.region == "$stack" else (0, 24)
        if ptr.offset < low or ptr.offset + width > high or ptr.offset % width:
            raise Unsupported(f"Invalid aligned object access: {ptr}, {kind}")
        if writing and ptr.region in self.readonly:
            raise Unsupported("Write through read-only input")
        for (region, offset, cell_kind) in self.cells:
            if region != ptr.region:
                continue
            cell_width = 8 if cell_kind == "f64" else 4
            if max(offset, ptr.offset) < min(offset + cell_width, ptr.offset + width):
                if (offset, cell_kind) != (ptr.offset, kind):
                    raise Unsupported("Overlapping differently typed memory accesses")
        self.access_log.append(("write" if writing else "read", ptr.region, ptr.offset, kind))
        return ptr.region, ptr.offset, kind

    def load(self, ptr, kind):
        key = self.access(ptr, kind)
        if key not in self.cells:
            raise Unsupported("Uninitialized memory read")
        return self.cells[key]

    def store(self, ptr, kind, value):
        if kind == "f64" and (not z3.is_fp(value) or value.sort() != F64):
            raise Unsupported("Non-binary64 value stored as double")
        if kind == "i32" and not (isinstance(value, (int, Pointer)) or z3.is_bv(value) and value.size() == 32):
            raise Unsupported("Non-i32 value stored as i32")
        self.cells[self.access(ptr, kind, True)] = value

    def fork(self):
        return copy.deepcopy(self)

    def merge(self, other, condition):
        if self.cells.keys() != other.cells.keys():
            raise Unsupported("Conditional memory allocation or uninitialized branch")
        for key in self.cells:
            left, right = other.cells[key], self.cells[key]
            self.cells[key] = select(condition, left, right)
        self.access_log.extend(other.access_log)


def select(condition, left, right):
    if isinstance(left, Pointer) or isinstance(right, Pointer):
        if left != right:
            raise Unsupported("Conditional pointer selection")
        return left
    if isinstance(left, int) and isinstance(right, int) and left == right:
        return left
    return z3.simplify(z3.If(condition, left, right))


def floating(op, left, right=None):
    if not z3.is_fp(left) or left.sort() != F64 or (right is not None and (not z3.is_fp(right) or right.sort() != F64)):
        raise Unsupported("Floating operation type mismatch")
    operations = {"+": z3.fpAdd, "-": z3.fpSub, "*": z3.fpMul, "/": z3.fpDiv}
    if op == "sqrt":
        return z3.fpSqrt(RNE, left)
    if op in operations:
        return operations[op](RNE, left, right)
    raise Unsupported("Unsupported FP operation " + op)


def truth(value):
    if z3.is_bool(value):
        return value
    if z3.is_fp(value):
        return z3.Not(z3.fpEQ(value, ZERO))
    if isinstance(value, int):
        return z3.BoolVal(value != 0)
    if z3.is_bv(value) and value.size() == 32:
        return value != 0
    raise Unsupported("Unsupported truth conversion")


def function_nodes(ast, wanted):
    found = {}
    def visit(node):
        if node.get("kind") == "FunctionDecl" and node.get("name") in wanted and any(x.get("kind") == "CompoundStmt" for x in node.get("inner", [])):
            name = node["name"]
            if name in found:
                raise Unsupported("Duplicate source definition " + name)
            found[name] = node
        for child in node.get("inner", []):
            visit(child)
    visit(ast)
    return found


def initial_state(function):
    memory, env, inputs = Memory(), {}, {}
    for parameter in function["inner"]:
        if parameter["kind"] != "ParmVarDecl":
            continue
        kind, name = parameter["type"]["qualType"], parameter["name"]
        if kind not in {"const double *", "double *"}:
            raise Unsupported("Unsupported parameter " + kind)
        env[name] = Pointer(name)
        for i in range(3):
            value = z3.FP(f"{name}_{i}", F64)
            inputs[f"{name}_{i}"] = value
            memory.store(Pointer(name, 8*i), "f64", value)
        if kind == "const double *":
            memory.readonly.add(name)
    return memory, env, inputs


class Source:
    def __init__(self, function, memory, env):
        self.function, self.memory, self.env = function, memory, dict(env)
        self.result = None
        self.returned = False

    def expression(self, node):
        kind, inner = node["kind"], node.get("inner", [])
        if kind == "ParenExpr":
            if len(inner) != 1:
                raise Unsupported("Malformed parentheses")
            return self.expression(inner[0])
        if kind == "ImplicitCastExpr":
            if len(inner) != 1:
                raise Unsupported("Malformed cast")
            value, cast = self.expression(inner[0]), node["castKind"]
            if cast == "LValueToRValue":
                return self.memory.load(value, "f64") if isinstance(value, Pointer) and node["type"]["qualType"] == "double" else value
            if cast == "FloatingToBoolean":
                return truth(value)
            if cast in {"NoOp", "FunctionToPointerDecay"}:
                return value
            raise Unsupported("Unsupported cast " + cast)
        if kind == "DeclRefExpr":
            reference = node["referencedDecl"]
            if reference["kind"] == "FunctionDecl" and reference["name"] == "sqrt":
                return "sqrt"
            if reference["name"] not in self.env:
                raise Unsupported("Unknown variable")
            return self.env[reference["name"]]
        if kind == "IntegerLiteral":
            return int(node["value"])
        if kind == "FloatingLiteral" and node["type"]["qualType"] == "double":
            return z3.FPVal(node["value"], F64)
        if kind == "ArraySubscriptExpr":
            base, offset = map(self.expression, inner)
            if not isinstance(base, Pointer) or not isinstance(offset, int):
                raise Unsupported("Unsupported source array index")
            return base.add(offset * 8)
        if kind == "BinaryOperator":
            if node["opcode"] == "=":
                ptr, value = map(self.expression, inner)
                self.memory.store(ptr, "f64", value)
                return value
            left, right = map(self.expression, inner)
            return floating(node["opcode"], left, right)
        if kind == "CompoundAssignOperator" and node["opcode"] == "/=":
            ptr, right = map(self.expression, inner)
            value = floating("/", self.memory.load(ptr, "f64"), right)
            self.memory.store(ptr, "f64", value)
            return value
        if kind == "CallExpr":
            args = list(map(self.expression, inner))
            if len(args) == 2 and args[0] == "sqrt":
                return floating("sqrt", args[1])
            raise Unsupported("Unsupported source call")
        raise Unsupported("Unsupported AST expression " + kind)

    def statement(self, node):
        kind, inner = node["kind"], node.get("inner", [])
        if self.returned:
            raise Unsupported("Statement after source return")
        if kind == "CompoundStmt":
            for child in inner:
                self.statement(child)
        elif kind == "DeclStmt":
            for decl in inner:
                if decl["kind"] != "VarDecl" or decl["type"]["qualType"] not in {"double", "const double"} or len(decl.get("inner", [])) != 1:
                    raise Unsupported("Unsupported variable declaration")
                self.env[decl["name"]] = self.expression(decl["inner"][0])
        elif kind == "ReturnStmt":
            self.result = self.expression(inner[0]) if inner else None
            self.returned = True
        elif kind == "IfStmt":
            if len(inner) not in {2, 3}:
                raise Unsupported("Unsupported source if")
            condition = truth(self.expression(inner[0]))
            left = Source(self.function, self.memory.fork(), self.env)
            right = Source(self.function, self.memory.fork(), self.env)
            left.statement(inner[1])
            if len(inner) == 3:
                right.statement(inner[2])
            if left.returned or right.returned or left.env.keys() != right.env.keys():
                raise Unsupported("Conditional declarations or returns")
            right.memory.merge(left.memory, condition)
            self.memory = right.memory
            self.env = {key: select(condition, left.env[key], right.env[key]) for key in left.env}
        else:
            self.expression(node)

    def execute(self):
        bodies = [x for x in self.function["inner"] if x["kind"] == "CompoundStmt"]
        if len(bodies) != 1:
            raise Unsupported("Expected one source body")
        self.statement(bodies[0])
        return self.result, self.memory
