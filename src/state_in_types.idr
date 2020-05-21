-- Alternate definition of Instruction that relies on types to
-- encapsulate change in state
import deceq_state
import Data.Vect

-- this instruction set is very limited but demonstrates basic functionality,
-- aside from the obvious omission of branching operations

-- an Instruction is a Type constructed by
-- initial MachineState and the MachineState after execution of the instruction
data Instruction : MachineState -> MachineState -> Type where
    MovI : (rd : Fin 32) -> (imm : Int) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd imm rs) flags) -- MovI changes state by replacing a single element of the register vector and incrementing the pc
    AddI : (rd : Fin 32) -> (rn : Fin 32) -> (imm : Int) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd (imm + (index rn rs)) rs) flags)
    Add : (rd : Fin 32) -> (rn : Fin 32) -> (rm : Fin 32) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd ((index rn rs) + (index rm rs)) rs) flags)
    Mov : (rd : Fin 32) -> (rn : Fin 32) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd (index rn rs) rs) flags)
    Mul : (rd : Fin 32) -> (rn : Fin 32) -> (rm : Fin 32) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd ((index rn rs) * (index rm rs)) rs) flags)
    (>>=) : Instruction s0 s1 -> Instruction s1 s2 -> Instruction s0 s2 -- useful monad-ish bind function for composing multiple instructions into one

-- this program's type expresses that it changes the initial state
-- in *precisely* the following manner:
-- pc is incremented 3 times, and the first three registers are replaced with 5, 8, 13
test_prog : Instruction (St pc ([r0,r1,r2] ++ rs) flags) (St (3 + pc) ([5,8,13] ++ rs) flags)
test_prog = MovI 0 5 >>= AddI 1 0 3 >>= Add 2 0 1

-- this program's type guarantees that r0 and r2 contain the
-- same value after execution (and, incidentally, that none
-- of the other values change)
test_2 : Instruction (St pc ([r0,r1,r2] ++ rs) flags) (St (1 + pc) ([r0,r1,r0] ++ rs) flags)
test_2 = Mov 2 0

-- this program's type ensures that the *only* thing this program
-- does to the MachineState is square the first register value
square_instruction : Instruction (St pc (r0::rs) flags) (St (1+pc) ((r0*r0)::rs) flags)
square_instruction = Mul 0 0 0
