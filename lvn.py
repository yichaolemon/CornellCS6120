from mycfg import blocks_by_label, form_blocks, blocks_to_json
import json
import sys

COMMUTATIVE_OPS = set(["add","mul"])
EVAL_OPS = set(["id","add","sub","div","mul"])


"""
Capabilities:
- copy propagation
- CSE exploiting commutativity
- id/constant propagation and folding
"""
class LVN:
    def __init__(self):
        # map from variable to value number
        self.environment = {}
        # index is the value number, items are tuples (value, canonical variable)
        self.value_table = []
        # key is value, value is value number
        self.value_to_number = {}

    def make_value(self, instr):
        op = instr["op"]
        if op == "const":
            return (op, instr["value"])
        args = instr["args"]
        arg_numbers = [self.environment[arg] for arg in args]
        if op in COMMUTATIVE_OPS:
            arg_numbers.sort()
        return (op, tuple(arg_numbers))

    def add_instr(self, instr):
        if "dest" not in instr:
            # assume there's a side effect, and this isn't a value
            return
        dest = instr["dest"]
        value = self.make_value(instr)
        if value in self.value_to_number:
            number = self.value_to_number[value]
        elif value[0] == "id":
            number = value[1][0]
            self.value_to_number[value] = number
        else:
            number = len(self.value_table)
            self.value_table.append((value, dest))
            self.value_to_number[value] = number
        self.environment[dest] = number

    def eval(self, op, operands):
        if op == "mul":
            return operands[0] * operands[1]
        elif op == "add":
            return operands[0] + operands[1]
        elif op == "sub":
            return operands[0] - operands[1]
        elif op == "div":
            if operands[1] == 0:
                raise Exception("division by zero")
            return operands[0] // operands[1]
        elif op == "id":
            return operands[0]
        else:
            raise Exception("eval not yet implemented for op:{}".format(op))

    def is_var_constant(self, var):
        return self.value_table[self.environment[var]][0][0] == "const"

    def reconstruct_instr(self, instr):
        if "op" not in instr or "args" not in instr:
            # label instr 
            return
        value = self.make_value(instr)
        # if value already exists and has a diff canonical variable representation
        if "dest" in instr:
            canonical_var = self.value_table[self.value_to_number[value]][1]
            if canonical_var != instr["dest"]:
                instr["op"] = "id"
                instr["args"] = [canonical_var]
        # replace each var in args with canonical 
        if "args" in instr:
            instr["args"] = [self.value_table[arg_num][1] for arg_num in value[1]]
        # id/const propagation and folding
        if "op" in instr and instr["op"] in EVAL_OPS:
            op = instr["op"]
            canonical_vars = instr["args"]
            if all(self.is_var_constant(var) for var in canonical_vars):
                operands = [self.value_table[self.environment[var]][0][1] for var in canonical_vars]
                try:
                    new_const_val = self.eval(op, operands)
                    instr["op"] = "const"
                    instr.pop("args", None)
                    instr["value"] = new_const_val
                    if "dest" in instr:
                        dest_var = instr["dest"]
                        self.value_table[self.environment[dest_var]] = (("const", new_const_val), dest_var)
                        del self.value_to_number[value]
                except Exception as ex:
                    pass

# find defs not used or later overwritten
def delete_deadcode(block):
    # map from variable to instr index
    defs = {}
    instr_to_delete = set()
    for i, instr in enumerate(block):
        # check usage
        args = instr["args"] if "args" in instr else []
        for var in args:
            if var in defs:
                del defs[var]
        # check defs
        if "dest" in instr:
            if instr["dest"] in defs:
                instr_to_delete.add(defs[instr["dest"]])
            defs[instr["dest"]] = i

    instr_to_delete |= set(defs.values())
    # assemble new block
    new_block = []
    for i, instr in enumerate(block):
        if i not in instr_to_delete:
            new_block.append(instr)
    return new_block

# iterate until convergence
def delete_deadcode_converge(block):
    prev = block
    new = delete_deadcode(prev)
    while prev != new:
        prev = new
        new = delete_deadcode(prev)
    return new

def lvn_block(block):
    # compute local value numbering and modifies block in place
    lvn = LVN()

    for instr in block:
        lvn.add_instr(instr)
        lvn.reconstruct_instr(instr)


def lvn():
    prog = json.load(sys.stdin)
    for func in prog['functions']:
        block_by_label, labels = blocks_by_label(form_blocks(func['instrs']))
        new_block_by_label= {}
        for k, block in block_by_label.items():
            lvn_block(block)
            new_block = delete_deadcode_converge(block)
            new_block_by_label[k] = new_block

        func["instrs"] = blocks_to_json(labels, new_block_by_label)
    print(json.dumps(prog))


if __name__ == '__main__':
    lvn()
