import deceq_state
import Data.Vect

-- data Instruction : MachineState -> MachineState -> Type where
    -- AddI_r1_r1 : (imm : Int) -> Instruction (St pc (r1::registers) flags) (St (pc + 1) ((r1 + imm)::registers) flags)

-- data Instruction : MachineState -> MachineState -> Type where
--     MovI : (imm : Int) -> (d : Nat) -> Instruction (St pc [r0,r1,r2,r3,r4,r5,r6,r7] flags)
--                                                    (St (pc + 1) [r0,r1,r2,r3,r4,r5,r6,r7] flags)

data Instruction : MachineState -> MachineState -> Type where
    MovI : (rd : Fin 32) -> (imm : Int) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd imm rs) flags)
    AddI : (rd : Fin 32) -> (rn : Fin 32) -> (imm : Int) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd (imm + (index rn rs)) rs) flags)
    Add : (rd : Fin 32) -> (rn : Fin 32) -> (rm : Fin 32) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd ((index rn rs) + (index rm rs)) rs) flags)
    Mov : (rd : Fin 32) -> (rn : Fin 32) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd (index rn rs) rs) flags)
    Mul : (rd : Fin 32) -> (rn : Fin 32) -> (rm : Fin 32) -> Instruction (St pc rs flags)
                                                   (St (1 + pc) (replaceAt rd ((index rn rs) * (index rm rs)) rs) flags)
    -- B : (offset : Int) -> Instruction (St pc rs flags) (St (pc + offset) rs flags)
    -- BEq : (offset : Int) -> Instruction (St pc rs 0) (St (pc + offset) rs 0)
    -- BEq : (offset : Int) -> Instruction (St pc rs flags) (St (pc + 1) rs flags)
    (>>=) : Instruction s0 s1 -> Instruction s1 s2 -> Instruction s0 s2

test_prog : Instruction (St pc ([r0,r1,r2] ++ rs) flags) (St (3 + pc) ([5,8,13] ++ rs) flags)
test_prog = MovI 0 5 >>= AddI 1 0 3 >>= Add 2 0 1

test_2 : Instruction (St pc ([r0,r1,r2] ++ rs) flags) (St (1 + pc) ([r0,r1,r0] ++ rs) flags)
test_2 = Mov 2 0

square_instruction : Instruction (St pc (r0::rs) flags) (St (1+pc) ((r0*r0)::rs) flags)
square_instruction = Mul 0 0 0
