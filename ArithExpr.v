Require Import ZArith.
Require Import List.

Inductive bop : Set :=
| Add : bop
| Sub : bop
| Mul : bop.

Definition arg := nat.

Fixpoint mkArg (name : nat) : arg := name.
Fixpoint argName (a : arg) : nat := a.

Inductive aexp : Set :=
| ArgExp : arg -> aexp
| Binop : bop -> aexp -> aexp -> aexp.

Open Scope Z_scope.

Definition arithState := arg -> Z.

Fixpoint aEval (e : aexp) (s : arithState) : Z :=
  match e with
    | Binop Add l r => (aEval l s) + (aEval r s)
    | Binop Sub l r => (aEval l s) - (aEval r s)
    | Binop Mul l r => (aEval l s) * (aEval r s)
    | ArgExp a => s a
  end.

Definition stackReg := nat.

Fixpoint stackRegName (sreg : stackReg) : nat := sreg.
Fixpoint eq_stackReg (sr1 sr2 : stackReg) : bool :=
  beq_nat (stackRegName sr1) (stackRegName sr2).

Fixpoint mkStackReg (n : nat) : stackReg := n.

Inductive stackBOP : Set :=
| StackAdd : stackBOP
| StackSub : stackBOP
| StackMul : stackBOP.

Inductive stackInstr : Set :=
| Push : stackReg -> stackInstr
| Pop : stackReg -> stackInstr
| StackBinop : stackBOP -> stackReg -> stackReg -> stackInstr
| Ret : stackReg -> stackInstr.

Definition stackRegVals := stackReg -> Z.
Definition stack := list Z.

Inductive stackState : Set :=
| StackState : stackRegVals -> stack -> stackState.

Definition arithStateToStackRegVals (arithS : arithState) : stackRegVals :=
  fun sreg => arithS (argName (stackRegName sreg)).

Definition freshStackState (arithS : arithState) : stackState :=
  StackState (arithStateToStackRegVals arithS) nil.

Check arithStateToStackRegVals.

Definition stackProgram := list stackInstr.

Fixpoint pushStk (r : stackReg) (ss : stackState) : stackState :=
  match ss with
    | StackState srVals stk => StackState srVals ((srVals r) :: stk)
  end.

Fixpoint popStk (r : stackReg) (ss : stackState) : option stackState :=
  match ss with
    | StackState srVals (v :: stk) =>
      Some (StackState (fun x => if eq_stackReg x r then v else srVals x) stk)
    | StackState srVals nil =>
      None
  end.

Fixpoint spEval (sp : stackProgram) (ss : stackState) : option Z :=
  match sp, ss with
    | nil, _ => None
    | (Push r :: sp'), ss =>
      spEval sp' (pushStk r ss)
    | (Pop r :: sp'), ss =>
      match popStk r ss with
        | Some newSS => spEval sp' newSS
        | None => None
      end
    | (StackBinop b r0 r1 :: sp'), (StackState srVals stk) =>
      spEval sp' (StackState srVals stk)
    | Ret r :: sp', (StackState srVals stk) => Some (srVals r)
  end.

Definition sr0 := mkStackReg 0.
Definition sr1 := mkStackReg 1.

Fixpoint arithToStackInstrs (e : aexp) : list stackInstr :=
  match e with
    | ArgExp a => Push (mkStackReg (argName a)) :: nil
    | Binop Add l r =>
      (arithToStackInstrs l) ++ (arithToStackInstrs r) ++ (Pop sr0 :: Pop sr1 :: StackBinop StackAdd sr0 sr1 :: nil)
    | Binop Sub l r =>
      (arithToStackInstrs l) ++ (arithToStackInstrs r) ++ (Pop sr0 :: Pop sr1 :: StackBinop StackSub sr0 sr1 :: nil)
    | Binop Mul l r =>
      (arithToStackInstrs l) ++ (arithToStackInstrs r) ++ (Pop sr0 :: Pop sr1 :: StackBinop StackMul sr0 sr1 :: nil)
  end.
  
Fixpoint compileArithToStack (e : aexp) : stackProgram :=
  (arithToStackInstrs e) ++ (Pop sr0 :: Ret sr0 :: nil).

(*Theorem compileArithToStack_correct :
  forall (e : aexp) (ss : arithState),
           Some (aEval e ss) = spEval (compileArithToStack e) (freshStackState ss).
Proof.*)
  