import json
import sys

TERMINATORS = 'jmp', 'br', 'ret'

def form_blocks(body):
    cur_block = []
    for instr in body:
        if 'op' in instr:
            cur_block.append(instr)
            if instr['op'] in TERMINATORS:
                yield cur_block
                cur_block = []
        else:  # a label
            if cur_block:
                yield cur_block
            cur_block = [instr]
    if cur_block:
        yield cur_block

def blocks_by_label(blocks):
    block_by_label = {}
    labels = []
    for block in blocks:
        first = block[0]
        if 'label' in first:
            name = first['label']
        else:
            name = "b{}".format(len(block_by_label))
        block_by_label[name] = block
        labels.append(name)

    return block_by_label, labels

def make_cfg(block_by_label, labels):
    # returns map from label to successor labels
    cfg = {}
    for i, label in enumerate(labels):
        last = block_by_label[label][-1]
        if last['op'] in ('jmp', 'br'):
            cfg[label] = last['labels']
        elif last['op'] == 'ret':
            cfg[label] = []
        else:
            if i < len(labels)-1:
                cfg[label] = [labels[i+1]]
            else:
                cfg[label] = []
    return cfg

def reachable_labels(cfg, start):
    reached = set()
    frontier = [start]
    while len(frontier) > 0:
        label = frontier.pop()
        if label in reached:
            continue
        reached.add(label)
        for neighbor in cfg[label]:
            frontier.append(neighbor)
    return reached

def remove_unreachable(cfg, labels, block_by_label):
    reachable = reachable_labels(cfg, labels[0])
    new_labels = []
    for label in labels:
        if label in reachable:
            new_labels.append(label)
        else:
            del block_by_label[label]
    return new_labels

def blocks_to_json(labels, block_by_label):
    instrs = []
    for label in labels:
        instrs.extend(block_by_label[label])
    return instrs

def mycfg():
    prog = json.load(sys.stdin)
    for func in prog['functions']:
        block_by_label, labels = blocks_by_label(form_blocks(func['instrs']))
        cfg = make_cfg(block_by_label, labels)
        labels = remove_unreachable(cfg, labels, block_by_label)
        func['instrs'] = blocks_to_json(labels, block_by_label)
    print(json.dumps(prog))

if __name__ == '__main__':
    mycfg()
