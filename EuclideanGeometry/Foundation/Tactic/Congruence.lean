import Lean.Meta.Basic
import Lean.Elab
import Lean.Message
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence
-- 添加的import，记得删除
import Qq
import EuclideanGeometry.Foundation.Axiom.Linear.Colinear

namespace EuclidGeom

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
--添加的open
open Qq
open Lean PrettyPrinter Delaborator SubExpr

def tryCloseMainGoal (candidate : List Expr) : TacticM Unit := do
  for e in candidate do
    try
      closeMainGoal e
    catch
    | _ => continue -- should show some information, if failed

def tryEvalExact (candidate : List Term) : TacticM Unit := do
  let goaltype ← getMainTarget
  IO.println s!"{candidate.length}"
  for t in candidate do
    let r ← elabTermEnsuringType t goaltype
    IO.println s!"Loop at {t}"
    IO.println s!"Try Block"
    try
      closeMainGoalUsing (checkUnassigned := false)
        fun type => do
          let mvarCounterSaved := (← getMCtx).mvarCounter
          let r ← elabTermEnsuringType t type
          logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
          return r
    catch
    | .error s mes =>
      IO.println s!"  {s}failed. {← mes.toString} continue"
      continue
    | _ =>
      IO.println s!"  failed. internal error. continue"
      continue
    IO.println s!"Not Catched, after try block"

-- the tactic `by_SAS`
syntax (name := SAS) "by_SAS" (ppSpace colGt term:max) (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

def mkSASSyntax (l : List Term) : Term := Syntax.mkApp (mkIdent `EuclidGeom.congr_of_SAS) (Array.mk l)

@[tactic SAS]
def evalSAS : Tactic := fun stx =>
  match stx with
  | `(tactic| by_SAS $t₁ $t₂ $t₃) => do
    let TermList : List Term := [t₁, t₂, t₃]
    let TermCandidate : List Term := List.map mkSASSyntax (TermList.permutations)
    IO.println s!"{TermCandidate}"
    tryEvalExact TermCandidate
    IO.println s!" Checkpoint2 reached"
  | _ => throwUnsupportedSyntax


example {P : Type _} [EuclideanPlane P] {tr_nd₁ tr_nd₂ : Triangle_nd P} (e₂ : tr_nd₁.1.edge₂.length = tr_nd₂.1.edge₂.length) (a₁ : tr_nd₁.angle₁.value = tr_nd₂.angle₁.value) (e₃ : tr_nd₁.1.edge₃.length = tr_nd₂.1.edge₃.length) : tr_nd₁.1 IsCongrTo tr_nd₂.1 := by
  sorry
  -- exact congr_of_SAS e₂ a₁ e₃
  -- by_SAS a₁ e₂ e₃

-- the tactic `by_add_comm`
syntax (name := by_add_comm) "by_add_comm" (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

def mkAddCommSyntax (l : List Term) : Term := Syntax.mkApp (mkIdent `Nat.add_comm) (Array.mk l)

@[tactic by_add_comm]
def evalByAddComm : Tactic := fun stx =>
  match stx with
  | `(tactic| by_add_comm $t₁ $t₂) => do
    let TermList : List Term := [t₁, t₂]
    let TermCandidate : List Term := List.map mkAddCommSyntax (TermList.permutations)
    IO.println s!"{TermCandidate}"
    tryEvalExact TermCandidate
    IO.println s!" Checkpoint2 reached"
  | _ => throwUnsupportedSyntax

example (m n : Nat) : n + m = m + n := by
sorry
  -- exact add_comm n m
  -- by_add_comm m n
  -- by_add_comm n m

syntax (name:= by_SAS') "by_SAS'" (ppSpace colGt term:max) (ppSpace colGt term:max) (ppSpace colGt term:max) : tactic

@[tactic by_SAS']
def evalBySAS' : Tactic := sorry

--以下为一些笔记，之后记得删除！

#check Option

def extractSegLengthEq : Q(Prop) →  MetaM (Option Unit)
  | ~q(@EuclidGeom.Seg.length _ (_) $x = @EuclidGeom.Seg.length _ (_) $y) => return .some ()
  | _ => return .none
-- 为什么我的报错这么奇怪
-- Angle value 也可以搞一个类似的，然后需要一个函数把他们组合起来

def extractAngleValueEq : Q(Prop) → MetaM (Option Unit)
  | ~q(@EuclidGeom.Angle.value _ (_) $x = @EuclidGeom.Angle.value _ (_) $y) => return .some ()
  | _ => return .none
--注：这里的函数 EG.Angle.value 都是从下面需要的类型中来的（e₃,a₁等等）

def liftOrElse : MetaM (Option Unit) → MetaM (Option Unit) → MetaM (Option Unit) :=
  fun xs ys => do match ← xs with
    | .some x => return x
    | .none => do match ←  ys with
      | .some y => return y
      | .none => return .none
-- 注释：← 是bind，我们需要在match前写do，如果不写 do的话会bind到前面去

def extractSaEq : TacticM (List Name) := do
  let lCtx ← getLCtx
  let mut xs := []
  for decl in lCtx do
      if decl.isImplementationDetail
        then continue
        else do
        match ← liftOrElse (extractSegLengthEq decl.type) (extractAngleValueEq decl.type) with
        | .some _ => xs := decl.userName :: xs
        | .none => continue
  return xs
--为什么会报错呢？ 好像少import了一些东西


syntax (name := sas') "sas'" (ppSpace colGt term:max)* : tactic

@[tactic sas']
def evalSas' : Tactic := fun stx =>
  match stx with
  | `(tactic| sas' $x0 $x1 $x2) => do
    for xs in List.permutations' [x0, x1, x2] do
      let lCtx <- getLCtx
      for decl in lCtx do
        if decl.isImplementationDetail
          then continue
        else do
        logInfo f!"user name : {decl.userName}"
        logInfo f!"type: {decl.type}"
    sorry
      --法一s
      --match xs with
      --  | [x0, x1, x2] => sorry
      --法二
      -- let t <- `(tactic| refine congr_of_SAS $x0 $x1 $x2)
     -- debug : 加logInfo s!"debug term:{t}"
      -- try
      -- evalTactic t
      --加return（为了在解决goal的时候弹出tactic？）
      -- catch_ => continue
      -- logInfo "sas' doesn't solve any goal"
      -- return
  | _ => throwUnsupportedSyntax

-- 问题：首先在尝试完策略之后要加报错
-- 不能自己找条件
-- 首先：如何从上下文中读取条件
-- 有哪些API 是干这个事情的
-- getLCtx
-- 使用： 可以let一个local contex 然后使用for in 语句
#check LocalContext
--#check userName?
-- 函数UserName

--想把上下文中所有有关边相等和角相等的条件拿出来
-- 我们只关心条件的类型，再来match
-- 而type ： LocalDecl → Expr
-- 但是我们发现打印出来的Expr 非常长
-- 加一个函数 extractSegLengthEq
-- 之后我们需要写一个拿假说的函数

-- 如何在所有的列表中拿到3个其中的条件
-- 使用三次for in： for x0 in congrDeclNames do
-- 但是这个时候不能直接用$x0 来调用
-- 需要加一句话来把x0变成syntax？？
-- let x0 := mkIdent x0

--接下来考虑加入多种全等策略

def congrSalemmas : List Name :=
  [``congr_of_SAS
  ,``congr_of_ASA
  ]
-- 在后文中考虑把原来二点congr_of SAS 换成一个$f,
-- f 用 for in 在 congrSalemmas 中取出，并如上做转换到 syntax


--接下来看delab的工作方法

--先看Options
#check DataValue
#check 1 + 1
set_option pp.explicit true in
-- pp 美观打印
#check 1 + 1
-- 把所有东西都显式表达出来
#check 1 + 1
--这里表示 in指的是暂时使用，之后就不会pp.explicit了

-- 网课： 怎么创建，怎么查询，

-- 再看delabration
-- 一个例子： 可以把product的表示转化成别的东西，并且overwrite掉之前的记号
-- 检索并重写？把一个Expr变成一个syntax

def foo : Nat → Nat := fun x => 42

@[delab app.foo]
def delabFoo : Delab := do
  `(1)
-- 注释：此处app.可以换成Expr中的东西?
-- @【】里面的是对应
-- 为什么会报错呢？ 要多加信息验证这个是monad吗？(open 了一个东西就行了)

--delab 其实用的并不多，更多的是unexpender

--现在想注册一个属性，使得我们用三角形全等的时候，这里的定理可以直接检索注册过的定理
-- 上面是中心化的注册：这些定理构成一张表，我们去找可以用哪个（这个一般是我们写TACTIC要用的）
-- 非中心化的注册

-- 关于自动化： Aesop


--可以试的练习
