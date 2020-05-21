import Data.Vect
import deceq_state

data BinOp = Add | Sub | Mul | Div

data CBOp = CBZ | CBNZ | BL

-- TODO: Use types to make sure register
-- numbers are less than 32
-- Update: I think I've accomplished this with the Fin class
Register : Type
Register = Fin 32

data Instruction = R BinOp Register Register Register |
                   I BinOp Int Register Register |
                   B String |
                   CB CBOp String Register |
                   MOVI Int Register |
                   MOV Register Register |
                   CMP Register Register|
                   L String -- pseudoinstruction for labels

-- MOVI 5 3
-- R Sub 1 3 4

-- MOVI -5 3
-- R Add 1 3 4

-- ^ prove that they're the same



-- ensures that labels can be search for within a program
Eq Instruction where
  (L l1) == (L l2) = l1 == l2
  _ == _ = False

Program : Type
Program = List Instruction

modulus_test : Program
modulus_test = [
  MOVI 102 0,     -- x0 = 102
  MOVI 5 1,      -- x1 = 5
  L "while",
  CMP 0 1, -- flags = x0 - x1
  CB BL "endwhile" 0, -- if flags is negative branch to endwhile
  R Sub 0 1 0, -- x0 = x0 - x1
  B "while",
  L "endwhile" -- should return 2
  ]

tiny_test : Program
tiny_test = [
  MOVI 20 0,
  MOVI 5 1,
  R Sub 0 1 2,
  CMP 0 2
  ]

factorial_test : Program
factorial_test = [
  MOVI 5 0,
  MOVI 1 1,
  MOVI 2 2,
  L "while",
  CMP 0 2,
  CB BL "endwhile" 0,
  R Mul 1 2 1,
  I Add 1 2 2,
  B "while",
  L "endwhile",
  MOV 1 0
  ]


initial_state : MachineState
initial_state = St 0 (replicate 32 0) 0

binop_exec : BinOp -> Int -> Int -> Int
binop_exec Add rm rn = rm + rn
binop_exec Sub rm rn = rm - rn
binop_exec Mul rm rn = rm * rn
binop_exec Div rm rn = rm `div` rn



-- one step of execution
-- TODO: branch with link
execute' : MachineState -> Program -> MachineState
execute' (St pc regs flags) prog = case cur of
    Nothing => Terminated -- this means the pc is outside of the program vector
                          -- thus the program is finished
    Just (B label) => branch label
    Just (CB op label rt) => condbranch op label rt
    Just inst => exec (St pc regs flags) inst
  where
    cur : Maybe Instruction
    cur = index' pc prog

    branch : String -> MachineState
    branch label' = case elemIndex (L label') prog of
        Nothing => Failed -- good spot for Failed state to be an error message
        Just pc' => St pc' regs flags

    condbranch : CBOp -> String -> Register -> MachineState
    condbranch op' label' rt' = if (satisfied op' rt')
        then branch label'
        else St (pc + 1) regs flags
      where
        satisfied : CBOp -> Register -> Bool
        satisfied CBZ rt'' = (index rt'' regs) == 0
        satisfied CBNZ rt'' = (index rt'' regs) /= 0
        satisfied BL _ = flags < 0

    -- simple (non-branch) executions
    exec : MachineState -> Instruction -> MachineState
    exec Failed _ = Failed
    exec (St pc regs flags) (R op rm rn rd) =
      St (pc + 1) (replaceAt rd
        (binop_exec op (index rm regs) (index rn regs)) regs) flags
    exec (St pc regs flags) (I op x rm rd) =
      St (pc + 1) (replaceAt rd
        (binop_exec op x (index rm regs)) regs) flags
    exec (St pc regs flags) (MOVI x rd) = St (pc + 1) (replaceAt rd x regs) flags
    exec (St pc regs flags) (MOV rm rd) =
      St (pc + 1) (replaceAt rd (index rm regs) regs) flags
    exec (St pc regs flags) (CMP rm rn) =
      St (pc + 1) regs ((index rm regs) - (index rn regs))
    exec (St pc regs flags) (L _) = St (pc + 1) regs flags
      -- labels just get skipped

-- clean version that does not require an initial state
execute : Program -> MachineState
execute = execute'' initial_state where
  -- continue execution until a terminated or failed state is reached
  execute'' : MachineState -> Program -> MachineState
  execute'' state prog = case execute' state prog of
    Terminated => state
    Failed => Failed
    state' => execute'' state' prog
