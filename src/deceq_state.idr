module deceq_state

-- attempting to show equality between two MachineStates
import Data.Vect

-- exactly what it looks like
%default total

-- type synonyms
-- TODO: ensure that the PC is within the length of the program
-- update: maybe nevermind? b/c detecting program temination
-- depends on the pc being greater than the length f the program
-- sized values?
public export
PC : Type
PC = Nat

-- could I do something fancy here? maybe
public export
Flags : Type
Flags = Int


-- A state has a program counter, a vector of 32 integer registers,
-- and an additional int for comparison flags
-- included a failed state to reduce clutter of Maybes
-- failed state could be expanded for more detailed error reporting.
-- also thinking about having the Terminated state return what's in x0.
-- currently the only possible runtime error is an unfound label

-- TODO: 32 or 64 bit integers in the registers
public export
data MachineState = St PC (Vect 32 Int) Flags | Failed | Terminated

-- is there a way to show that many of these proofs are the same?
terminatedNotFailed : (Terminated = Failed) -> Void
terminatedNotFailed Refl impossible

failedNotTerminated : (Failed = Terminated) -> Void
failedNotTerminated Refl impossible

terminatedNotRunning : (Terminated = (St pc xs flags)) -> Void
terminatedNotRunning Refl impossible

failedNotRunning : (Failed = (St pc xs flags)) -> Void
failedNotRunning Refl impossible

runningNotTerminated : ((St pc xs flags) = Terminated) -> Void
runningNotTerminated Refl impossible

runningNotFailed : ((St pc xs flags) = Failed) -> Void
runningNotFailed Refl impossible
-- ^ this seems like way too much boilerplate

-- two states are the same only if proof can be provided that
-- their pc, registers, and flags are the same
-- was very helpful that Nat, Int, and Vect all implement DecEq
eqState : (pc = pc') -> (xs = xs') -> (flags = flags') ->
          (St pc xs flags = St pc' xs' flags')
eqState prf1 prf2 prf3 = rewrite prf1 in
                         rewrite prf2 in
                         rewrite prf3 in
                         Refl

-- ((Z = Z) -> Void) is a proof type
-- BUT
-- it is also a function from the reflexive property to the Void type
-- what this means:
-- applying that function to something of the type (Z = Z) generates an
-- instance of void
-- which is the equivalent of introducing 2 contradictory premises to
-- a mathematical proof
-- so it's a contradiction
Uninhabited ((Z = Z) -> Void) where
  uninhabited contra = contra Refl

-- showing two running states are not equal
diffPcDiffState : ((pc = pc') -> Void) ->
                  (St pc xs flags = St pc' xs' flags') -> Void
diffPcDiffState contra Refl = contra Refl

diffRegistersDiffState : ((xs = xs') -> Void) ->
                         (St pc xs flags = St pc' xs' flags') -> Void
diffRegistersDiffState contra Refl = contra Refl

diffFlagsDiffState : ((flags = flags') -> Void) ->
                         (St pc xs flags = St pc' xs' flags') -> Void
diffFlagsDiffState contra Refl = contra Refl

public export
DecEq MachineState where
  decEq Terminated Terminated = Yes Refl
  decEq Terminated Failed = No terminatedNotFailed
  decEq Terminated (St pc xs flags) = No terminatedNotRunning
  decEq Failed Failed = Yes Refl
  decEq Failed Terminated = No failedNotTerminated
  decEq Failed (St pc xs flags) = No failedNotRunning
  decEq (St pc xs flags) Terminated = No runningNotTerminated
  decEq (St pc xs flags) Failed = No runningNotFailed
  decEq (St pc xs flags) (St pc' xs' flags') = case decEq pc pc' of
    No contra1 => No (diffPcDiffState contra1)
    Yes prf1 => case decEq xs xs' of
      No contra2 => No (diffRegistersDiffState contra2)
      Yes prf2 => case decEq flags flags' of
        No contra3 => No (diffFlagsDiffState contra3)
        Yes prf3 => Yes (eqState prf1 prf2 prf3)

st1 : MachineState
st1 = St 0 (replicate 32 0) 0
st2 : MachineState
st2 = St 0 (replicate 32 0) 1
