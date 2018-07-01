Require Import String.
Require Import ZArith.
Require Import ZArith Int.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Require Import List.
Require Import Nat.


Fixpoint pow n m :=
  match m with
    | 0 => 1
    | S m => n * (n^m)
  end
where "n ^ m" := (pow n m) : nat_scope.

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' => match u with
                | 0 => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition div x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.



Definition modulo x y :=
  match y with
    | 0 => y
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Definition lt (x : Z) (y : Z) : Z := 
  match Z.ltb x y with
    | false => 0
    | true => 1
  end.
Definition gt (x : Z) (y : Z) : Z := 
  match Z.gtb x y with
    | false => 0
    | true => 1
  end.
Definition eq (x : Z) (y : Z) : Z := 
  match Z.sub x y with
    | 0%Z => 1
    | _ => 0
  end.

Definition slt (x : nat) (y : nat) := 1.
Definition sgt (x : nat) (y : nat) := 1.

Definition iszero (x : nat) := 
  match x with
    | 0 => 1
    | _ => 0
  end.

Definition memory  := Z -> Z.
Definition updateMemory (m : memory) (addr : Z) (value : Z) :=
  fun x => if (Z.eqb x addr) then value else (m x).
Definition myMemory :=
  fun _:Z =>
    0%Z.

Fixpoint mstore (m : memory) (n1 : Z) (n2 : Z) (limit : nat) : memory :=  (* limit will be 32*)
  match limit with
    | 0 => m
    | S n' => mstore (updateMemory m (Z.add (Z.of_nat n') n1) n2) n1 n2 n'
  end.

Definition storage  := Z -> Z.
Definition updateStorage (s : storage) (addr : Z) (value : Z) :=
  fun x => if (Z.eqb x addr) then value else (s x).
Definition myStorage :=
  fun _:Z =>
    0%Z.

Fixpoint sstore (s : storage) (n1 : Z) (n2 : Z) (limit : nat) : storage :=  (* limit will be 32*)
  match limit with
    | 0 => s
    | S n' => sstore (updateStorage s (Z.add (Z.of_nat n') n1) n2) n1 n2 n'
  end.

(*Eval compute in (mstore myMemory 5%Z 78%Z 1) 5%Z.*)

(*Eval compute in myMemory 452.*)
(*Definition updatedMyMemory := updateMemory myMemory 1243 15.
Definition updateddMyMemory := updateMemory updatedMyMemory 12443 1565.*)
Definition envf (x : Z) := 1%Z.
(*Eval compute in Z.of_nat (length (1%Z :: 2%Z :: nil)).*)
(*Fixpoint nth (n : nat) (l : list nat) : option nat := if (Nat.ltb n (length l)) then Some (List.nth n l 0) else None.*)

Inductive instr : Set :=
(* STOP AND ARITHMETIC OPERATIONS *)
| STOP : instr
| ADD : instr
| MUL : instr
| DIV : instr
| SDIV : instr
| SUB : instr
| MOD : instr
| SMOD : instr
| ADDMOD : instr
| MULMOD : instr
| EXP : instr
| SIGNEXTEND : instr
(* STOP AND ARITHMETIC OPERATIONS /*)

(* COMPARISON & BIWISE LOGIC OPERATIONS *)
| LT : instr
| GT : instr
| SLT : instr 
| SGT : instr
| EQ : instr
| ISZERO : instr
| AND : instr
| OR : instr
| XOR : instr
| NOT : instr
| BYTE : instr
(* COMPARISON & BIWISE LOGIC OPERATIONS /*)

(* ENVIRONMENTAL INFORMATION *)
| ADDRESS : instr
| BALANCE : instr
| ORIGIN : instr
| CALLER : instr
| CALLVALUE : instr
| CALLDATALOAD : instr
| CALLDATASIZE : instr
| CALLDATACOPY : instr
| CODESIZE : instr
| CODECOPY : instr
| GASPRICE : instr
| EXTCODESIZE : instr
| EXTCODECOPY : instr
| RETURNDATASIZE : instr
| RETURNDATACOPY : instr
 (* ENVIRONMENTAL INFORMATION /*)

(* Stack, Memory, Storage and Flow Operations *)
 | POP : instr
 | MLOAD : instr
 | MSTORE : instr
 | MSTORES : instr
 | SLOAD : instr
 | SSTORE : instr
 | JUMP : instr
 | JUMPI : instr
 | PC : instr
 | MSIZE : instr
 | GAS : instr
 | JUMPDEST : instr
(* Stack, Memory, Storage and Flow Operations /*)
| DUP1 : instr
| DUP2 : instr
| DUP3 : instr
| DUP4 : instr
| DUP5 : instr
| DUP6 : instr
| DUP7 : instr
| DUP8 : instr
| DUP9 : instr
| DUP10 : instr
| DUP11 : instr
| DUP12 : instr
| DUP13 : instr
| DUP14 : instr
| DUP15 : instr
 | SWAP1 : instr
 | SWAP2 : instr
 | SWAP3 : instr
 | SWAP4 : instr
 | SWAP5 : instr
 | SWAP6 : instr
 | SWAP7 : instr
 | SWAP8 : instr
 | SWAP9 : instr
 | SWAP10 : instr
 | SWAP11 : instr
 | SWAP12 : instr
 | SWAP13 : instr
 | SWAP14 : instr
 | SWAP15 : instr
 | SWAP16 : instr
| PUSH1 : Z -> instr
| PUSH2 : Z -> instr
| PUSH3 : Z -> instr
| PUSH4 : Z -> instr
| PUSH5 : Z -> instr
| PUSH6 : Z -> instr
| PUSH7 : Z -> instr
| PUSH8 : Z -> instr
| PUSH9 : Z -> instr
| PUSH10 : Z -> instr
| PUSH11 : Z -> instr
| PUSH12 : Z -> instr
| PUSH13 : Z -> instr
| PUSH14 : Z -> instr
| PUSH15 : Z -> instr
| PUSH16 : Z -> instr
| PUSH17 : Z -> instr
| PUSH18 : Z -> instr
| PUSH19 : Z -> instr
| PUSH20 : Z -> instr
| PUSH21 : Z -> instr
| PUSH22 : Z -> instr
| PUSH23 : Z -> instr
| PUSH24 : Z -> instr
| PUSH25 : Z -> instr
| PUSH26 : Z -> instr
| PUSH27 : Z -> instr
| PUSH28 : Z -> instr
| PUSH29 : Z -> instr
| PUSH30 : Z -> instr
| PUSH31 : Z -> instr
| PUSH32 : Z -> instr
| REVERT : instr
| RETURN : instr
| NOTHING.


Fixpoint n_th (A:list instr)(n: nat) : instr :=
  match A with
    | x :: A' =>
    match n with
      | 0 => x
      | _ => n_th A' (n-1)
    end
    | nil => NOTHING
  end.

(*gas price cost for every instruction*)
Fixpoint C (instruction : instr) : nat :=
match instruction with
 (* STOP AND ARITHMETIC OPERATIONS *)
 | STOP => 1
 | ADD => 1
 | MUL => 1
 | SUB => 1
 | DIV => 1
 | SDIV => 1
 | MOD => 1
 | SMOD => 1
 | ADDMOD => 1
 | MULMOD => 1
 | EXP => 1
 | SIGNEXTEND => 1
 (* STOP AND ARITHMETIC OPERATIONS /*)

  (*COMPARISON & BIWISE LOGIC OPERATIONS *)
 | LT => 1
 | GT => 1
 | SLT => 1
 | SGT => 1
 | EQ => 1
 | ISZERO => 1
 | AND => 1
 | OR => 1
 | XOR => 1
 | NOT => 1
 | BYTE => 1
 (* COMPARISON & BIWISE LOGIC OPERATIONS /*)

 (* ENVIRONMENTAL INFORMATION *)
 | ADDRESS => 1
 | BALANCE => 1
 | ORIGIN => 1
 | CALLER => 1
 | CALLVALUE => 1
 | CALLDATALOAD => 1
 | CALLDATASIZE => 1
 | CALLDATACOPY => 1
 | CODESIZE => 1
 | CODECOPY => 1
 | GASPRICE => 1
 | EXTCODESIZE => 1
 | EXTCODECOPY => 1
 | RETURNDATASIZE => 1
 | RETURNDATACOPY => 1
 (* ENVIRONMENTAL INFORMATION /*)

 (* Stack, Memory, Storage and Flow Operations /*)
 | POP => 1
 | MLOAD => 1
 | MSTORE => 1
 | MSTORES => 1
 | SLOAD => 1
 | SSTORE => 1
 | JUMP => 1
 | JUMPI => 1
 | PC => 1
 | MSIZE => 1
 | GAS => 1
 | JUMPDEST => 1
 (* Stack, Memory, Storage and Flow Operations /*)
 | DUP1 => 1
 | DUP2 => 1
 | DUP3 => 1
 | DUP4 => 1
 | DUP5 => 1
 | DUP6 => 1
 | DUP7 => 1
 | DUP8 => 1
 | DUP9 => 1
 | DUP10 => 1
 | DUP11 => 1
 | DUP12 => 1
 | DUP13 => 1
 | DUP14 => 1
 | DUP15 => 1
 | SWAP1 => 1
 | SWAP2 => 1
 | SWAP3 => 1
 | SWAP4 => 1
 | SWAP5 => 1
 | SWAP6 => 1
 | SWAP7 => 1
 | SWAP8 => 1
 | SWAP9 => 1
 | SWAP10 => 1
 | SWAP11 => 1
 | SWAP12 => 1
 | SWAP13 => 1
 | SWAP14 => 1
 | SWAP15 => 1
 | SWAP16 => 1
 | PUSH1 n => 1
 | PUSH2 n => 1
 | PUSH3 n => 1
 | PUSH4 n => 1
 | PUSH5 n => 1
 | PUSH6 n => 1
 | PUSH7 n => 1
 | PUSH8 n => 1
 | PUSH9 n => 1
 | PUSH10 n => 1
 | PUSH11 n => 1
 | PUSH12 n => 1
 | PUSH13 n => 1
 | PUSH14 n => 1
 | PUSH15 n => 1
 | PUSH16 n => 1
 | PUSH17 n => 1
 | PUSH18 n => 1
 | PUSH19 n => 1
 | PUSH20 n => 1
 | PUSH21 n => 1
 | PUSH22 n => 1
 | PUSH23 n => 1
 | PUSH24 n => 1
 | PUSH25 n => 1
 | PUSH26 n => 1
 | PUSH27 n => 1
 | PUSH28 n => 1
 | PUSH29 n => 1
 | PUSH30 n => 1
 | PUSH31 n => 1
 | PUSH32 n => 1
 | REVERT => 1
 | RETURN => 1
 | NOTHING => 0
end.


(*                    Ia  Io   Ip      Id       Is   Iv        Ib           IH       Ie     Iw       *)
Inductive I := myI : Z -> Z -> Z -> list nat -> Z -> Z -> list instr -> list nat -> nat -> nat -> I.
Inductive Stack := myStack : list Z -> Stack.
(*Inductive State := myState : Stack -> I -> nat -> State .*)
(*                              g      pc   memory     storage         i       stack     *)
Inductive State := myState : nat -> nat -> memory -> storage -> nat -> Stack -> State.
Inductive Environment := myEnv : State -> nat -> I -> Environment.
Definition initialI := myI 67%Z 23%Z 34%Z (23 :: 12 :: nil) 65%Z 53%Z 

(*
PALINDROM

pragma solidity ^0.4.21;

contract Ballot{
    function is_palindrom(int n) public returns(bool)
    {
    	int n1;
    	int d;
    	int rn=0;
    	n1=n;
    	while(n>0)
    	{
    		d=n%10;
    		rn=(rn*10)+d;
    		n/=10;
    	}
    	return n1==rn;
    }
    bool result = is_palindrom(45654);
}

*)

(PUSH1 96 :: PUSH1 64 :: MSTORE :: PUSH2 15 :: PUSH2 45654 :: PUSH2 46 :: PUSH5 4294967296 :: MUL :: PUSH2 123 :: OR :: PUSH5 4294967296 :: SWAP1 :: DIV :: JUMP :: JUMPDEST :: PUSH1 0 :: DUP1 :: PUSH2 256 :: EXP :: DUP2 :: SLOAD :: DUP2 :: PUSH1 255 :: MUL :: NOT :: AND :: SWAP1 :: DUP4 :: ISZERO :: ISZERO :: MUL :: OR :: SWAP1 :: SSTORE :: POP :: CALLVALUE :: ISZERO :: PUSH2 43 :: JUMPI :: PUSH1 0 :: DUP1 :: REVERT :: JUMPDEST :: PUSH2 108 :: JUMP :: JUMPDEST :: PUSH1 0 :: DUP1 :: PUSH1 0 :: DUP1 :: PUSH1 0 :: SWAP1 :: POP :: DUP5 :: SWAP3 :: POP :: JUMPDEST :: PUSH1 0 :: DUP6 :: SGT :: ISZERO :: PUSH2 95 :: JUMPI :: PUSH1 10 :: DUP6 :: DUP2 :: ISZERO :: ISZERO :: PUSH2 71 :: JUMPI :: JUMPDEST :: SMOD :: SWAP2 :: POP :: DUP2 :: PUSH1 10 :: DUP3 :: MUL :: ADD :: SWAP1 :: POP :: PUSH1 10 :: DUP6 :: DUP2 :: ISZERO :: ISZERO :: PUSH2 89 :: JUMPI :: JUMPDEST :: SDIV :: SWAP5 :: POP :: PUSH2 57 :: JUMP :: JUMPDEST :: DUP1 :: DUP4 :: EQ :: SWAP4 :: POP :: POP :: POP :: POP :: SWAP2 :: SWAP1 :: POP :: JUMP :: JUMPDEST :: PUSH1 242 :: DUP1 :: PUSH2 167 :: PUSH1 0 :: CODECOPY :: PUSH1 0 :: RETURN :: STOP :: PUSH1 0 :: SLOAD :: nil)

nil 674 33.
Definition initialStack := myStack nil.
Definition initialState := myState 1000 0 myMemory myStorage 0 initialStack.

Definition initialEnv := myEnv initialState 1000 initialI.
Open Scope Z.
Fixpoint run_instr (instruction : instr) (state: State) (gas : nat) (I : I) : State :=
match state with
| myState g pc m s i stack =>
  match stack with
  | myStack stck =>  
    match instruction with
      (* STOP AND ARITHMETIC OPERATIONS *)
      | STOP => match stck with
               | s' => myState (g-C(ADD)) (pc+1) m s i (myStack (s'))
               end
      | ADD => match stck with
               | n1 :: n2 :: s' => myState (g-C(ADD)) (pc+1) m s i (myStack (Z.add n1 n2 :: s'))
               | _ => state
               end
      | MUL => match stck with
               | n1 :: n2 :: s' => myState (g-C(MUL)) (pc+1) m s i (myStack (Z.mul n1 n2 :: s'))
               | _ => state
               end
      | SUB => match stck with
               | n1 :: n2 :: s' => myState (g-C(MUL)) (pc+1) m s i (myStack (Z.sub n1 n2 :: s'))
               | _ => state
               end
      | DIV => match stck with
               | n1 :: n2 :: s' => myState (g-C(DIV)) (pc+1) m s i (myStack (Z.div n1 n2 :: s'))
               | _ => state
               end
      | SDIV => match stck with
               | n1 :: n2 :: s' => myState (g-C(DIV)) (pc+1) m s i (myStack (Z.div n1 n2 :: s'))
               | _ => state
               end
      | MOD => match stck with
               | n1 :: n2 :: s' => myState (g-C(DIV)) (pc+1) m s i (myStack (Z.modulo n1 n2 :: s'))
               | _ => state
               end
      | SMOD => match stck with
               | n1 :: n2 :: s' => myState (g-C(DIV)) (pc+1) m s i (myStack (Z.modulo n1 n2 :: s'))
               | _ => state
               end
      | ADDMOD => match stck with
               | n1 :: n2 :: s' => myState (g-C(DIV)) (pc+1) m s i (myStack (Z.modulo (Z.add n1 n2) (Z.pow 2 256) :: s'))
               | _ => state
               end
      | MULMOD => match stck with
               | n1 :: n2 :: s' => myState (g-C(DIV)) (pc+1) m s i (myStack (Z.mul n1 n2 :: s'))
               | _ => state
               end
      | EXP => match stck with
               | n1 :: n2 :: s' => myState (g-C(EXP)) (pc+1) m s i (myStack (Z.pow n1 n2 :: s'))
               | _ => state
               end
      | SIGNEXTEND => state
      (* STOP AND ARITHMETIC OPERATIONS /*)

      (* COMPARISON & BIWISE LOGIC OPERATIONS *)
     
      | LT => match stck with
               | n1 :: n2 :: ss' => myState (g-C(LT)) (pc+1) m s i (myStack ((lt n1 n2) :: ss'))
               | _ => state
               end
      | GT => match stck with
               | n1 :: n2 :: tt' => myState (g-C(GT)) (pc+1) m s i (myStack ((gt n1 n2) :: tt'))
               | _ => state
               end
      | SLT => match stck with
               | n1 :: n2 :: uu' => myState (g-C(SLT)) (pc+1) m s i (myStack ((lt n1 n2) :: uu'))
               | _ => state
               end
      | SGT => match stck with
               | n1 :: n2 :: vv' => myState (g-C(SGT)) (pc+1) m s i (myStack ((gt n1 n2) :: vv'))
               | _ => state
               end
      | EQ => match stck with
               | n1 :: n2 :: rr' => myState (g-C(EQ)) (pc+1) m s i (myStack ((eq n1 n2) :: rr'))
               | _ => state
               end
      | ISZERO => match stck with
               | n1 :: s' => myState (g-C(ISZERO)) (pc+1) m s i (myStack (eq 0 n1 :: s'))
               | _ => state
               end
      | AND => match stck with
               | n1 :: n2 :: s' => myState (g-C(AND)) (pc+1) m s i (myStack ((Z.land n1 n2) :: s'))
               | _ => state
               end
      | OR => match stck with
               | n1 :: n2 :: s' => myState (g-C(OR)) (pc+1) m s i (myStack ((Z.lor n1 n2) :: s'))
               | _ => state
               end
      | XOR => match stck with
               | n1 :: n2 :: s' => myState (g-C(XOR)) (pc+1) m s i (myStack ((Z.lxor n1 n2) :: s'))
               | _ => state
               end
      | NOT => match stck with
               | n1 :: ss' => myState (g-C(NOT)) (pc+1) m s i (myStack ((Z.lnot n1) :: ss'))
               | _ => state
               end
      | BYTE => match stck with
               | n1 :: n2 :: s' => myState (g-C(BYTE)) (pc+1) m s i (myStack (101101010 :: s'))
               | _ => state
               end
      (* COMPARISON & BIWISE LOGIC OPERATIONS /*)


      (* ENVIRONMENT INFORMATION *)
      | ADDRESS => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(ADDRESS)) (pc+1) m s i (myStack (Ia :: stck))
                  end
      | BALANCE => match stck with
               | n1 :: s' => myState (g-C(BALANCE)) (pc+1) m s i (myStack (69%Z :: s'))
               | _ => state
               end
      | ORIGIN => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(ORIGIN)) (pc+1) m s i (myStack (Io :: stck))
                  end
      | CALLER => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(CALLER)) (pc+1) m s i (myStack (Is :: stck))
                  end
      | CALLVALUE => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(CALLVALUE)) (pc+1) m s i (myStack (Iv :: stck))
                  end
      | CALLDATALOAD => match stck with
               | n1 :: s' => myState (g-C(CALLDATALOAD)) (pc+1) m s i (myStack (69%Z :: s'))
               | _ => state
               end
      | CALLDATASIZE => match stck with
               | s' => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(CALLDATALOAD)) (pc+1) m s i (myStack ((Z.of_nat (length Id)) :: s'))
                  end
               end
      | CALLDATACOPY => match stck with
               | n1 :: n2 :: n3 :: s' => myState (g-C(CALLDATACOPY)) (pc+1) m s i (myStack (69%Z :: s'))
               | _ => state
               end
      | CODESIZE => match stck with
               | s' => myState (g-C(CODESIZE)) (pc+1) m s i (myStack (1000%Z :: s'))
               end
      | CODECOPY => match stck with
               | n1 :: n2 :: n3 :: s' => myState (g-C(CODECOPY)) (pc+1) m s i (myStack (s'))
               | _ => state
               end
      | GASPRICE => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(GASPRICE)) (pc+1) m s i (myStack (Ip :: stck))
                  end
      | EXTCODESIZE => match stck with
               | n1 :: s' => myState (g-C(EXTCODESIZE)) (pc+1) m s i (myStack (34%Z :: s'))
               | _ => state
               end
      | EXTCODECOPY => match stck with
               | n1 :: n2 :: n3 :: n4 :: s' => myState (g-C(EXTCODECOPY)) (pc+1) m s i (myStack ( s'))
               | _ => state
               end
      | RETURNDATASIZE => match I with
                  | myI Ia Io Ip Id Is Iv Ib IH Ie Iw => myState (g-C(RETURNDATASIZE)) (pc+1) m s i (myStack (2000%Z :: stck))
                  end
      | RETURNDATACOPY => match stck with
               | n1 :: n2 :: n3 :: s' => myState (g-C(RETURNDATACOPY)) (pc+1) m s i (myStack ( s'))
               | _ => state
               end
      (* ENVIRONMENT INFORMATION /*)

      (* Stack, Memory, s and Flow Operations *)
       | POP => match stck with
               | n1 :: s' => myState (g-C(POP)) (pc+1) m s i (myStack s')
               | _ => state
               end
      | MLOAD => match stck with
               | n1 :: s' => myState (g-C(MLOAD)) (pc+1) m s i (myStack ((m n1) :: s'))
               | _ => state
               end
      | MSTORE => match stck with
                     | n1 :: n2 :: s' => myState (g-C(MSTORE)) (pc+1) (mstore m n1 n2 1) s i (myStack (s'))
                     | _ => state
                     end
      | MSTORES => match stck with
                     | n1 :: s' => myState (g-C(MSTORES)) (pc+1) m s i (myStack ((envf n1) :: s'))
                     | _ => state
                     end
      | SLOAD => match stck with
                     | n1 :: s' => myState (g-C(SLOAD)) (pc+1) m s i (myStack ((s n1) :: s'))
                     | _ => state
                     end
      | SSTORE => match stck with
                     | n1 :: n2 :: s' => myState (g-C(SSTORE)) (pc+1) m ((sstore s n1 n2 1)) i (myStack (s'))
                     | _ => state
                     end
      | PC => match stck with
                           | n1 :: s' => myState (g-C(PC)) (pc+1) m s i (myStack ((envf n1) :: s'))
                           | _ => state
                           end
      | MSIZE => match stck with
                           | n1 :: s' => myState (g-C(MSIZE)) (pc+1) m s i (myStack ((envf n1) :: s'))
                           | _ => state
                           end
      | GAS => match stck with
                           | n1 :: s' => myState (g-C(GAS)) (pc+1) m s i (myStack ((envf n1) :: s'))
                           | _ => state
                           end
      | JUMPDEST => match stck with
                           | s' => myState (g-C(JUMPDEST)) (pc+1) m s i (myStack ( s'))
                           end
      (* Stack, Memory, s and Flow Operations /*)

      | PUSH1 n => myState (g-C(PUSH1 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH2 n => myState (g-C(PUSH2 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH3 n => myState (g-C(PUSH3 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH4 n => myState (g-C(PUSH4 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH5 n => myState (g-C(PUSH5 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH6 n => myState (g-C(PUSH6 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH7 n => myState (g-C(PUSH7 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH8 n => myState (g-C(PUSH8 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH9 n => myState (g-C(PUSH9 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH10 n => myState (g-C(PUSH10 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH11 n => myState (g-C(PUSH11 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH12 n => myState (g-C(PUSH12 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH13 n => myState (g-C(PUSH13 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH14 n => myState (g-C(PUSH14 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH15 n => myState (g-C(PUSH15 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH16 n => myState (g-C(PUSH16 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH17 n => myState (g-C(PUSH17 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH18 n => myState (g-C(PUSH18 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH19 n => myState (g-C(PUSH19 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH20 n => myState (g-C(PUSH20 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH21 n => myState (g-C(PUSH21 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH22 n => myState (g-C(PUSH22 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH23 n => myState (g-C(PUSH23 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH24 n => myState (g-C(PUSH24 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH25 n => myState (g-C(PUSH25 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH26 n => myState (g-C(PUSH26 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH27 n => myState (g-C(PUSH27 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH28 n => myState (g-C(PUSH28 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH29 n => myState (g-C(PUSH29 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH30 n => myState (g-C(PUSH30 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH31 n => myState (g-C(PUSH31 n)) (pc+1) m s i (myStack (n :: stck))
      | PUSH32 n => myState (g-C(PUSH32 n)) (pc+1) m s i (myStack (n :: stck))

      | DUP1 => match stck with
                           | n1 :: s' => myState (g-C(DUP1)) (pc+1) m s i (myStack (n1 :: n1 :: s'))
                           | _ => state
                           end
      | DUP2 => match stck with
                                 | n1 :: n2 :: s' => myState (g-C(DUP2)) (pc+1) m s i (myStack (n2 :: n1 :: n2 :: s'))
                                 | _ => state
                                 end
      | DUP3 => match stck with
                                 | n1 :: n2 :: n3 :: s' => myState (g-C(DUP3)) (pc+1) m s i (myStack (n3 :: n1 :: n2 :: n3 :: s'))
                                 | _ => state
                                 end
      | DUP4 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: s' => myState (g-C(DUP4)) (pc+1) m s i (myStack (n4 :: n1 :: n2 :: n3 :: n4 :: s'))
                                 | _ => state
                                 end
      | DUP5 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: s' => myState (g-C(DUP5)) (pc+1) m s i (myStack (n5 :: n1 :: n2 :: n3 :: n4 :: n5 :: s'))
                                 | _ => state
                                 end
      | DUP6 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: s' => myState (g-C(DUP6)) (pc+1) m s i (myStack (n6 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: s'))
                                 | _ => state
                                 end
      | DUP7 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: s' => myState (g-C(DUP7)) (pc+1) m s i (myStack (n7 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: s'))
                                 | _ => state
                                 end
      | DUP8 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: s' => myState (g-C(DUP8)) (pc+1) m s i (myStack (n8 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: s'))
                                 | _ => state
                                 end
      | DUP9 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: s' => myState (g-C(DUP9)) (pc+1) m s i (myStack (n9 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: s'))
                                 | _ => state
                                 end
      | DUP10 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: s' => myState (g-C(DUP10)) (pc+1) m s i (myStack (n10 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: s'))
                                 | _ => state
                                 end
      | DUP11 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: s' => myState (g-C(DUP11)) (pc+1) m s i (myStack (n11 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: s'))
                                 | _ => state
                                 end
      | DUP12 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: s' => myState (g-C(DUP12)) (pc+1) m s i (myStack (n12 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: s'))
                                 | _ => state
                                 end
      | DUP13 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: s' => myState (g-C(DUP13)) (pc+1) m s i (myStack (n13 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: s'))
                                 | _ => state
                                 end
      | DUP14 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: s' => myState (g-C(DUP14)) (pc+1) m s i (myStack (n14 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: s'))
                                 | _ => state
                                 end
      | DUP15 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: s' => myState (g-C(DUP15)) (pc+1) m s i (myStack (n15 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: s'))
                                 | _ => state
                           end
      | SWAP1 => match stck with
                           | n1 :: n2 :: s' => myState (g-C(SWAP1)) (pc+1) m s i (myStack (n2 :: n1 :: s'))
                           | _ => state
                           end
      | SWAP2 => match stck with
                                 | n1 :: n2 :: n3 :: s' => myState (g-C(SWAP2)) (pc+1) m s i (myStack (n3 :: n2 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP3 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: s' => myState (g-C(SWAP3)) (pc+1) m s i (myStack (n4 :: n2 :: n3 :: n1 :: s'))
                                 | s' => myState g (pc+1) m s i (myStack (s'))
                                 end
      | SWAP4 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: s' => myState (g-C(SWAP4)) (pc+1) m s i (myStack (n5 :: n2 :: n3 :: n4 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP5 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: s' => myState (g-C(SWAP5)) (pc+1) m s i (myStack (n6 :: n2 :: n3 :: n4 :: n5 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP6 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: s' => myState (g-C(SWAP6)) (pc+1) m s i (myStack (n7 :: n2 :: n3 :: n4 :: n5 :: n6 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP7 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: s' => myState (g-C(SWAP7)) (pc+1) m s i (myStack (n8 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP8 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: s' => myState (g-C(SWAP8)) (pc+1) m s i (myStack (n9 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP9 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: s' => myState (g-C(SWAP9)) (pc+1) m s i (myStack (n10 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP10 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: s' => myState (g-C(SWAP10)) (pc+1) m s i (myStack (n11 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP11 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: s' => myState (g-C(SWAP11)) (pc+1) m s i (myStack (n12 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP12 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: s' => myState (g-C(SWAP12)) (pc+1) m s i (myStack (n13 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP13 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: s' => myState (g-C(SWAP13)) (pc+1) m s i (myStack (n14 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP14 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: s' => myState (g-C(SWAP14)) (pc+1) m s i (myStack (n15 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP15 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: n16 :: s' => myState (g-C(SWAP15)) (pc+1) m s i (myStack (n16 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: n1 :: s'))
                                 | _ => state
                                 end
      | SWAP16 => match stck with
                                 | n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: n16 :: n17 :: s' => myState (g-C(SWAP16)) (pc+1) m s i (myStack (n17 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: n9 :: n10 :: n11 :: n12 :: n13 :: n14 :: n15 :: n16 :: n1 :: s'))
                                 | _ => state
                                 end
      | JUMP => match stck with
           | n1 :: s' => myState (g-C(JUMP)) (Z.to_nat n1) m s i (myStack (s'))
           | _ => state
           end
      | JUMPI => match stck with
           | n1 :: 0%Z :: s' => myState (g-C(JUMP)) (pc+1) m s i (myStack (s'))
           | n1 :: n2 :: s' => myState (g-C(JUMP)) (Z.to_nat n1) m s i (myStack (s'))
           | _ => myState g 0 m s i stack
           end
      | REVERT => match stck with
                  | n1 :: n2 :: s' => myState (g-C(REVERT)) (pc+1) m s i (myStack s')
                  | _ => state
                  end
      | RETURN => match stck with
                  | n1 :: n2 :: s' => myState (g-C(RETURN)) (pc+1) m s i (myStack s')
                  | _ => state
                  end
      | NOTHING => state
    end
  end
end.
Close Scope Z.

(*Eval compute in run_instr (PUSH1 7) nil.*)

Fixpoint run (env : Environment) : Environment :=
  match env with
  | myEnv state gas I =>
    match I with
      | myI Ia Io Ip Id Is Iv Ib IH Ie Iw =>
         match state with
           | myState g pc m s i stack => myEnv (run_instr (n_th Ib pc) state gas I) (gas) I
         end
     end
  end.


Fixpoint runpgm (env : Environment) (gas : nat) : Environment :=
  match env with
  | myEnv state g I =>
   match gas with
    | 0 => myEnv state 10000 I
    | S gas' =>runpgm (run (myEnv state (gas-1) I)) gas'
     end
  end.

(*Lemma correct_property:
  forall E state g I g' pc m s i stack,
    runpgm initialEnv 256 = E ->
      E = myEnv state g I ->
        state = myState g' pc m s i stack ->
          s 0%Z = 1%Z.
   
Proof.
  intros.
  simpl in *.
  subst.
  inversion H0.
  unfold updateStorage.
  simpl.
  reflexivity.
Qed.*)

Eval compute in (runpgm initialEnv 258).