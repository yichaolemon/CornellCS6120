from mycfg import blocks_by_label, form_blocks, blocks_to_json
import json
import sys


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
        arg_numbers = tuple(self.environment[arg] for arg in args)
        return (op, arg_numbers)

    def add_instr(self, instr):
        if "dest" not in instr:
            # assume there's a side effect, and this isn't a value
            return
        dest = instr["dest"]
        value = self.make_value(instr)
        if value in self.value_to_number:
            number = self.value_to_number[value]
        else:
            number = len(self.value_table)
            self.value_table.append((value, dest))
            self.value_to_number[value] = number
        self.environment[dest] = number


    def reconstruct_instr(self, instr):
        # See if we can replace the whole value.
        if "dest" in instr:
            value = self.make_value(instr)
            canonical = self.value_table[self.value_to_number[value]][1]
            if canonical != instr["dest"]:
                instr["op"] = "id"
                instr["args"] = [canonical]
                return
        if "args" in instr:
            value = self.make_value(instr)
            instr["args"] = [self.value_table[number][1] for number in value[1]]

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
