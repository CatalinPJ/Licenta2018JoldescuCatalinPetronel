def stack_content(n): # for dup
    s="n1"
    for i in range(n-1):
        s+=" :: n{}".format(i+2)
    s+=" :: s'"
    return s

def stack_content_swap(n): # for swap
    s="n1"
    for i in range(n):
        s+=" :: n{}".format(i+2)
    s+=" :: s'"
    return s

def stack_content_swapped(n, n1, n2): # for swap
    s="n1"
    for i in range(n):
        s+=" :: n{}".format(i+2)
    s+=" :: s'"
    s = s.replace("n{}".format(n1), "_")
    s = s.replace("n{}".format(n2), "n{}".format(n1))
    s = s.replace("_", "n{}".format(n2))
    return s

# print(stack_content_swapped(7, 1, 8))
# for i in range (1,16):
#     print("| DUP{} => match stck with\n\
#                            | {} => myState (g-C(DUP{})) (pc+1) m i (myStack (n{} :: {}))\n\
#                            | _ => state\n\
#                            end".format(i, stack_content(i), i, i, stack_content(i)))

# for i in range(1,17):
#     print("| SWAP{} => match stck with\n\
#                            | {} => myState (g-C(SWAP{})) (pc+1) m i (myStack ({}))\n\
#                            | _ => state\n\
#                            end".format(i, stack_content_swap(i), i, stack_content_swapped(i, 1, i+1)))

# for i in range (1, 16):
#     print(" | SWAP{} : instr".format(i))
#
# for i in range (1, 16):
#     print(" | SWAP{} => 1".format(i))

import re

def hex_to_z(match_obj):
    return str(int(match_obj.group(0), 16))

def normalize_byte_code(byte_code_string):
    stop_op = "STOP"
    add_ap = "ADD"
    mul_op = "MUL"
    div_op = "DIV"
    sdiv_op = "SDIV"
    sub_op = "SUB"
    addmod_op = "ADDMOD"
    mulmod_op = "MULMOD"
    exp_op = "EXP"
    signextend_op = "SIGNEXTEND"

    dup_ops = ['DUP{}'.format(i) for i in range(1,16)]
    swap_ops = ['SWAP{}'.format(i) for i in range(1,17)]
    push_ops = ['PUSH{} 0x[0-9A-F]+'.format(i) for i in range(1, 33)]
    log_ops  = ['LOG{}'.format(i) for i in range(0,5)]
    ops = ["STOP", 'ADDMOD', 'MUL',' DIV', 'SDIV', 'SUB', 'ADDRESS', 'MULMOD', 'EXP', 'SIGNEXTEND',\
           'LT', 'GT','SLT', 'SGT', 'EQ', 'ISZERO', 'AND', 'OR', 'XOR', 'NOT', 'BYTE',\
           'ADD', 'BALANCE', 'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATALOAD', 'CALLDATASIZE', 'CALLDATACOPY', 'CODESIZE', 'CODECOPY', 'GASPRICE', 'EXTCODESIZE', 'EXTCODECOPY', 'RETURNDATASIZE', 'RETURNDATACOPY', 'RETURN', 'REVERT',\
           'POP', 'MLOAD', 'MSTORE', 'MSTORES', 'SLOAD', 'SSTORE', 'JUMPDEST', 'JUMPI', 'PC', 'MSIZE', 'GAS', 'JUMP'\
           ]
    ops += dup_ops
    ops += swap_ops
    ops += push_ops
    ops += log_ops

    regex_ops = "("
    for item in ops:
        regex_ops += "(" + item + ")" + "|"
    regex_ops = regex_ops [:-1] + ")"

    coq_ops_list = ''
    obj = re.finditer(regex_ops, byte_code_string)
    i = 1
    for op in obj:
        coq_ops_list += op.group(0) + " :: "
        print(i, re.sub("0x[0-9A-Fa-f]+", hex_to_z, op.group(0)))
        i += 1
    coq_ops_list = coq_ops_list [:-3]
    coq_ops_list = re.sub("0x[0-9A-Fa-f]+", hex_to_z, coq_ops_list)
    print(coq_ops_list)
    # print(len(coq_ops_list.split("::")))
    # print(regex_ops)


"""
contract Ballot {
    int p =7;
    function x(){
        int q = 89;
    }
}"""
# normalize_byte_code("PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x7 PUSH1 0x0 SSTORE CALLVALUE DUP1 ISZERO PUSH1 0xF JUMPI PUSH1 0x0 DUP1 REVERT JUMPDEST POP PUSH1 0x8D DUP1 PUSH2 0x23 PUSH1 0x0 CODECOPY PUSH1 0x0 RETURN STOP PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x4 CALLDATASIZE LT PUSH1 0x2D JUMPI PUSH1 0x0 CALLDATALOAD PUSH29 0x100000000000000000000000000000000000000000000000000000000 SWAP1 DIV PUSH4 0xFFFFFFFF AND DUP1 PUSH4 0xC55699C EQ PUSH1 0x31 JUMPI JUMPDEST PUSH1 0x0 DUP1 REVERT JUMPDEST CALLVALUE DUP1 ISZERO PUSH1 0x3A JUMPI PUSH1 0x0 DUP1 REVERT JUMPDEST POP PUSH1 0x3F PUSH1 0x41 JUMP JUMPDEST STOP JUMPDEST PUSH1 0x0 PUSH1 0x59 SWAP1 POP POP JUMP STOP LOG1 PUSH6 0x627A7A723058 KECCAK256 PUSH16 0x2EEAD6F9DB23C1705BDA91209B722B20 0xd9 CALLCODE 0x27 0xf 0x23 0xd 0xef PUSH15 0x2AF3C91B7096070029000000000000")

"""
contract Ballot {
    int r = 45;
    int p =7;
    function x(){
        int q = p;
    }
}"""
# normalize_byte_code("PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x2D PUSH1 0x0 SSTORE PUSH1 0x7 PUSH1 0x1 SSTORE CALLVALUE DUP1 ISZERO PUSH1 0x12 JUMPI PUSH1 0x0 DUP1 REVERT JUMPDEST POP PUSH1 0x8E DUP1 PUSH2 0x28 PUSH1 0x0 CODECOPY PUSH1 0x0 RETURN STOP PUSH1 0x80 PUSH1 0x40 MSTORE PUSH1 0x4 CALLDATASIZE LT PUSH1 0x30 JUMPI PUSH1 0x0 CALLDATALOAD PUSH29 0x100000000000000000000000000000000000000000000000000000000 SWAP1 DIV PUSH4 0xFFFFFFFF AND DUP1 PUSH4 0xC55699C EQ PUSH1 0x34 JUMPI JUMPDEST PUSH1 0x0 DUP1 REVERT JUMPDEST CALLVALUE DUP1 ISZERO PUSH1 0x3D JUMPI PUSH1 0x0 DUP1 REVERT JUMPDEST POP PUSH1 0x42 PUSH1 0x44 JUMP JUMPDEST STOP JUMPDEST PUSH1 0x0 PUSH1 0x1 SLOAD SWAP1 POP POP JUMP STOP LOG1 PUSH6 0x627A7A723058 KECCAK256 0xbf DUP7 0xb3 0x4b PUSH5 0xF3C4F1305D POP PUSH24 0xEBA8A2A51AFA0A39BEA30E5DE718777A5DB2D0DF00290000")

