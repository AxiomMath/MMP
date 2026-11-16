module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltBridgeEnd
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.ElementaryDltTermination
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.StepSequenceCycleRank
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantDltLiftNotNef
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltBridgeEndCrepantLift
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltModification
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.RelativeDltProgramNef

/-!
# Termination for projective lc fourfolds over `ℂ`

Let `(X, B)` be a projective lc fourfold pair over `ℂ` with rational boundary. Every program
from `(X, B)` (`MMP.Fourfold.Program`), with any successive choices of negative extremal rays,
birational contractions and permitted steps, has finitely many birational steps.

## Main results

* `MMP.Fourfold.Program.n_ne_top`: a program from a projective lc complex fourfold pair has
  finitely many birational steps.

## References

* [OAI4], Termination for projective lc fourfolds.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace Proof_prop_oai4_lc_lift

/-! ### Concatenating elementary steps -/

/-- A model of an elementary dlt program: a complex scheme with its structure morphism, a
canonical divisor and a boundary. -/
private structure DltModel where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  s : X ⟶ Spec (.of ℂ)
  K : Divisor X
  Δ : QDivisor X

attribute [local instance] DltModel.isIntegral DltModel.compactSpace DltModel.isLocallyNoetherian
  DltModel.isNormal

/-- The data of one elementary step between two models. -/
private structure StepRec where
  src : DltModel
  tgt : DltModel
  V : Scheme.{0}
  sV : V ⟶ Spec (.of ℂ)
  R : Set (NumericalCurveClasses src.s)
  f : src.X ⟶ V
  fp : tgt.X ⟶ V

/-- The step is an elementary dlt step. -/
private def StepRec.IsStep (r : StepRec) : Prop :=
  IsProjectiveElementaryDltStep r.src.s r.sV r.tgt.s r.src.K r.src.Δ r.R r.f r.fp r.tgt.Δ

private theorem exists_step_of_eq {A B T : DltModel} (h : A = B) {V : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} {fp : T.X ⟶ V}
    (H : ∃ (R : Set (NumericalCurveClasses B.s)) (f : B.X ⟶ V),
      IsProjectiveElementaryDltStep B.s sV T.s B.K B.Δ R f fp T.Δ) :
    ∃ (R : Set (NumericalCurveClasses A.s)) (f : A.X ⟶ V),
      IsProjectiveElementaryDltStep A.s sV T.s A.K A.Δ R f fp T.Δ := by
  subst h; exact H

/-- The `j`-th model of the concatenation of the steps `st`. -/
private noncomputable def glueModel (st : ℕ → StepRec) (j : ℕ) : DltModel :=
  ⟨modelSeq (st 0).src.X (fun i => (st i).tgt.X) j,
    modelStr (st 0).src.s (fun i => (st i).tgt.s) j,
    divisorSeq (st 0).src.K (fun i => (st i).tgt.K) j,
    divisorSeq (st 0).src.Δ (fun i => (st i).tgt.Δ) j⟩

private theorem glueModel_eq (st : ℕ → StepRec) (hchain : ∀ j, (st j).tgt = (st (j + 1)).src) :
    ∀ j, glueModel st j = (st j).src
  | 0 => rfl
  | j + 1 => hchain j

private theorem exists_glueStep (st : ℕ → StepRec) (hst : ∀ j, (st j).IsStep)
    (hchain : ∀ j, (st j).tgt = (st (j + 1)).src) (j : ℕ) :
    ∃ (R : Set (NumericalCurveClasses (glueModel st j).s)) (f : (glueModel st j).X ⟶ (st j).V),
      IsProjectiveElementaryDltStep (glueModel st j).s (st j).sV (st j).tgt.s
        (glueModel st j).K (glueModel st j).Δ R f (st j).fp (st j).tgt.Δ :=
  exists_step_of_eq (glueModel_eq st hchain j) ⟨_, _, hst j⟩

/-- The infinite elementary dlt program obtained by concatenating the chained steps `st`. -/
private noncomputable def glue (st : ℕ → StepRec) (hst : ∀ j, (st j).IsStep)
    (hchain : ∀ j, (st j).tgt = (st (j + 1)).src) :
    ElementaryDltProgram (st 0).src.s (st 0).src.K (st 0).src.Δ where
  n := ⊤
  Y i := (st i).tgt.X
  sY i := (st i).tgt.s
  KY i := (st i).tgt.K
  ΔY i := (st i).tgt.Δ
  R j := (exists_glueStep st hst hchain j).choose
  V j := (st j).V
  sV j := (st j).sV
  f j := (exists_glueStep st hst hchain j).choose_spec.choose
  fp j := (st j).fp
  isProjectiveQFactorialDltPair j _ :=
    (exists_glueStep st hst hchain j).choose_spec.choose_spec.isProjectiveQFactorialDltPair
  isProjectiveElementaryDltStep j _ := (exists_glueStep st hst hchain j).choose_spec.choose_spec

/-- There is no infinite chain of elementary dlt steps starting from a fourfold. -/
private theorem not_chain (st : ℕ → StepRec) (hst : ∀ j, (st j).IsStep)
    (hchain : ∀ j, (st j).tgt = (st (j + 1)).src)
    (hdim : topologicalKrullDim (st 0).src.X = 4) : False :=
  (glue st hst hchain).n_ne_top hdim rfl

/-- Walking through a sequence of nonempty bridges of lengths `m i`: the position `(i, k)`
(bridge `i`, step `k` within it) of the `j`-th step of their concatenation. -/
private def pos (m : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | j + 1 => if (pos m j).2 + 1 < m (pos m j).1 then ((pos m j).1, (pos m j).2 + 1)
      else ((pos m j).1 + 1, 0)

private theorem pos_lt (m : ℕ → ℕ) (hm : ∀ i, 0 < m i) : ∀ j, (pos m j).2 < m (pos m j).1
  | 0 => hm 0
  | j + 1 => by
    rw [show pos m (j + 1) = if (pos m j).2 + 1 < m (pos m j).1 then
      ((pos m j).1, (pos m j).2 + 1) else ((pos m j).1 + 1, 0) from rfl]
    split_ifs with h
    · exact h
    · exact hm _

/-- There is no infinite sequence of nonempty chained bridges of elementary dlt steps starting
from a fourfold. -/
private theorem not_bridges (m : ℕ → ℕ) (hm : ∀ i, 0 < m i) (loc : ℕ → ℕ → StepRec)
    (hloc : ∀ i k, k < m i → (loc i k).IsStep)
    (hin : ∀ i k, (loc i k).tgt = (loc i (k + 1)).src)
    (hacross : ∀ i, (loc i (m i)).src = (loc (i + 1) 0).src)
    (hdim : topologicalKrullDim (loc 0 0).src.X = 4) : False := by
  refine not_chain (fun j => loc (pos m j).1 (pos m j).2) (fun j => hloc _ _ (pos_lt m hm j))
    (fun j => ?_) hdim
  rw [hin, show pos m (j + 1) = if (pos m j).2 + 1 < m (pos m j).1 then
      ((pos m j).1, (pos m j).2 + 1) else ((pos m j).1 + 1, 0) from rfl]
  split_ifs with h
  · rfl
  · have : (pos m j).2 + 1 = m (pos m j).1 := le_antisymm (pos_lt m hm j) (not_lt.1 h)
    rw [this, hacross]

private theorem DltModel.mk_eq_mk {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {s s' : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {Δ : QDivisor X} (h : s = s') : (⟨X, s, K, Δ⟩ : DltModel) = ⟨X, s', K, Δ⟩ := by
  subst h; rfl

section Program

variable {U : Scheme.{0}} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
  {sU : U ⟶ Spec (.of ℂ)} {KU : Divisor U} {ΔU : QDivisor U}

/-- The `k`-th model of an elementary dlt program. -/
private noncomputable def progModel (Q : ElementaryDltProgram sU KU ΔU) (k : ℕ) : DltModel :=
  ⟨modelSeq U Q.Y k, modelStr sU Q.sY k, divisorSeq KU Q.KY k, divisorSeq ΔU Q.ΔY k⟩

/-- The `k`-th step of an elementary dlt program. -/
private noncomputable def progStep (Q : ElementaryDltProgram sU KU ΔU) (k : ℕ) : StepRec :=
  ⟨progModel Q k, progModel Q (k + 1), Q.V k, Q.sV k, Q.R k, Q.f k, Q.fp k⟩

private theorem progStep_isStep (Q : ElementaryDltProgram sU KU ΔU) {k : ℕ} (hk : (k : ℕ∞) < Q.n) :
    (progStep Q k).IsStep :=
  Q.isProjectiveElementaryDltStep k hk

end Program

/-! ### Lifting the program -/

section Lift

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}

/-- A crepant dlt lift of the `i`-th model of the program `P`, with a canonical divisor. -/
private structure Lift (P : Program sX K B) (i : ℕ) where
  U : Scheme.{0}
  [isIntegral : IsIntegral U]
  [compactSpace : CompactSpace U]
  [isLocallyNoetherian : IsLocallyNoetherian U]
  [isNormal : IsNormal U]
  p : U ⟶ modelSeq X P.Y i
  Δ : QDivisor U
  KU : Divisor U
  hlift : IsCrepantDltLift (modelStr sX P.sY i) (divisorSeq K P.KY i) (divisorSeq B P.BY i) p Δ
  hKU : ∃ n : ℕ, KU.IsCanonicalDivisor (p ≫ modelStr sX P.sY i) n

attribute [local instance] Lift.isIntegral Lift.compactSpace Lift.isLocallyNoetherian
  Lift.isNormal

variable (P : Program sX K B)

private theorem lt_n (hn : P.n = ⊤) (i : ℕ) : (i : ℕ∞) < P.n := hn ▸ ENat.coe_lt_top i

private theorem dim_modelSeq (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) :
    ∀ i, topologicalKrullDim (modelSeq X P.Y i) = 4
  | 0 => hdim
  | i + 1 =>
    ((P.isPermittedStep i (lt_n P hn i)).isFourfoldStepDiagram (dim_modelSeq hn hdim i)).dim_plus

variable {P}

/-- The lift of a fourfold model is a fourfold. -/
private theorem Lift.dim {i : ℕ} (L : Lift P i)
    (hdim : topologicalKrullDim (modelSeq X P.Y i) = 4) : topologicalKrullDim L.U = 4 := by
  have : MMP.Mori.IsVariety ℂ (L.p ≫ modelStr sX P.sY i) := L.hlift.isQFactorial.1.1
  have : MMP.Mori.IsVariety ℂ (modelStr sX P.sY i) := L.hlift.isProjectiveVariety.toIsVariety
  rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (modelStr sX P.sY i)
    (L.p ≫ modelStr sX P.sY i) L.hlift.isBirationalMorphism, hdim]

/-- The dlt bridge over `Z_i` of a lift of `X_i`: a nonempty elementary dlt program over `Z_i`
whose end is nef over `Z_i`. -/
private structure Bridge (P : Program sX K B) (i : ℕ) where
  L : Lift P i
  Q : RelativeElementaryDltProgram (L.p ≫ modelStr sX P.sY i) L.KU L.Δ (L.p ≫ P.f i)
  n_ne_zero : Q.n ≠ 0
  isRelativelyNef : (Divisor.toQDivisor (divisorSeq L.KU Q.KY Q.n.toNat) +
      divisorSeq L.Δ Q.ΔY Q.n.toNat).IsRelativelyNef (modelStr (L.p ≫ modelStr sX P.sY i) Q.sY
        Q.n.toNat) (modelMap (L.p ≫ P.f i) Q.hY Q.n.toNat)

private theorem exists_bridge (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) {i : ℕ}
    (L : Lift P i) :
    ∃ Q : RelativeElementaryDltProgram (L.p ≫ modelStr sX P.sY i) L.KU L.Δ (L.p ≫ P.f i),
      Q.n ≠ 0 ∧ (Divisor.toQDivisor (divisorSeq L.KU Q.KY Q.n.toNat) +
      divisorSeq L.Δ Q.ΔY Q.n.toNat).IsRelativelyNef (modelStr (L.p ≫ modelStr sX P.sY i) Q.sY
        Q.n.toNat) (modelMap (L.p ≫ P.f i) Q.hY Q.n.toNat) := by
  have hstep := P.isPermittedStep i (lt_n P hn i)
  obtain ⟨Q, hQ⟩ := IsCrepantDltLift.exists_relativeElementaryDltProgram_isRelativelyNef hstep
    (dim_modelSeq P hn hdim i) (dim_modelSeq P hn hdim (i + 1)) L.hlift L.hKU
  refine ⟨Q, fun h0 => ?_, hQ⟩
  have hm : Q.n.toNat = 0 := by rw [h0]; rfl
  revert hQ
  rw [hm]
  exact hstep.not_isRelativelyNef_of_isCrepantDltLift L.hlift L.hKU

/-- The end of a bridge over `Z_i` is a crepant dlt lift of `X_{i+1}`. -/
private theorem Bridge.exists_end (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) {i : ℕ}
    (hsmall : IsSmallMorphism (modelStr sX P.sY i) (P.sZ i) (P.f i)) (b : Bridge P i) :
    ∃ p' : modelSeq b.L.U b.Q.Y b.Q.n.toNat ⟶ modelSeq X P.Y (i + 1),
      p' ≫ modelStr sX P.sY (i + 1) = modelStr (b.L.p ≫ modelStr sX P.sY i) b.Q.sY b.Q.n.toNat ∧
      IsCrepantDltLift (modelStr sX P.sY (i + 1)) (divisorSeq K P.KY (i + 1))
        (divisorSeq B P.BY (i + 1)) p' (divisorSeq b.L.Δ b.Q.ΔY b.Q.n.toNat) ∧
      ∃ n : ℕ, MMP.Mori.Divisor.IsCanonicalDivisor (p' ≫ modelStr sX P.sY (i + 1)) n
        (divisorSeq b.L.KU b.Q.KY b.Q.n.toNat) := by
  have hstep := P.isPermittedStep i (lt_n P hn i)
  obtain ⟨p', hp'ℂ, hp'Z, hp'proj, hY, hp', hcrep⟩ :=
    hstep.exists_isCrepantBoundary_of_isRelativelyNef (dim_modelSeq P hn hdim i) b.L.hlift b.Q
      b.isRelativelyNef
  have hlift := IsCrepantDltLift.of_relativeElementaryDltProgram hstep (dim_modelSeq P hn hdim i)
    (dim_modelSeq P hn hdim (i + 1)) hsmall b.L.hlift b.Q p' hp'ℂ hp'Z hp'proj hp' hY hcrep
  rw [← P.KY_eq i (lt_n P hn i), ← P.BY_eq i (lt_n P hn i)] at hlift
  refine ⟨p', hp'ℂ, hlift, ?_⟩
  obtain ⟨n, hK⟩ := (b.Q.isProjectiveQFactorialDltPair _ (ENat.coe_toNat_le_self _)).isCanonicalDivisor
  exact ⟨n, (show p' ≫ modelStr sX P.sY (i + 1) = _ from hp'ℂ) ▸ hK⟩

/-- The lift of `X_{i+1}` at the nef end of a bridge over `Z_i`. -/
private noncomputable def Bridge.next (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) {i : ℕ}
    (hsmall : IsSmallMorphism (modelStr sX P.sY i) (P.sZ i) (P.f i)) (b : Bridge P i) :
    Lift P (i + 1) where
  U := modelSeq b.L.U b.Q.Y b.Q.n.toNat
  p := (b.exists_end hn hdim hsmall).choose
  Δ := divisorSeq b.L.Δ b.Q.ΔY b.Q.n.toNat
  KU := divisorSeq b.L.KU b.Q.KY b.Q.n.toNat
  hlift := (b.exists_end hn hdim hsmall).choose_spec.2.1
  hKU := (b.exists_end hn hdim hsmall).choose_spec.2.2

private theorem Bridge.next_comp (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) {i : ℕ}
    (hsmall : IsSmallMorphism (modelStr sX P.sY i) (P.sZ i) (P.f i)) (b : Bridge P i) :
    (b.next hn hdim hsmall).p ≫ modelStr sX P.sY (i + 1) =
      modelStr (b.L.p ≫ modelStr sX P.sY i) b.Q.sY b.Q.n.toNat :=
  (b.exists_end hn hdim hsmall).choose_spec.1

/-- Every model of the program has a crepant dlt lift. -/
private theorem nonempty_lift (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) (i : ℕ) :
    Nonempty (Lift P i) := by
  have hstep := P.isPermittedStep i (lt_n P hn i)
  obtain ⟨m, hK⟩ := hstep.isCanonicalDivisor
  have hm : m = 4 := by
    have h := hK.topologicalKrullDim_eq
    rw [dim_modelSeq P hn hdim i] at h
    exact_mod_cast h.symm
  subst hm
  obtain ⟨V, _, _, _, p, ΔV, hlift⟩ := exists_isCrepantDltLift (modelStr sX P.sY i)
    hstep.isProjectiveVariety (dim_modelSeq P hn hdim i) hK hstep.isLogCanonicalPair
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hlift.isProjectiveMorphism
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨n, KU, hKU, -⟩ := hlift.isDltPair.1.1.2
  exact ⟨{ U := V, p := p, Δ := ΔV, KU := KU, hlift := hlift, hKU := ⟨n, hKU⟩ }⟩

/-- The chosen bridge over `Z_i` of a lift of `X_i`. -/
private noncomputable def mkBridge (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) {i : ℕ}
    (L : Lift P i) : Bridge P i :=
  ⟨L, (exists_bridge hn hdim L).choose, (exists_bridge hn hdim L).choose_spec.1,
    (exists_bridge hn hdim L).choose_spec.2⟩

/-- The bridges over `Z_{i₀}, Z_{i₀ + 1}, …`, each starting at the end of the previous one. -/
private noncomputable def bridgeSeq (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) (i₀ : ℕ)
    (hsmall : ∀ i, i₀ ≤ i → IsSmallMorphism (modelStr sX P.sY i) (P.sZ i) (P.f i)) :
    ∀ i, Bridge P (i₀ + i)
  | 0 => mkBridge hn hdim (nonempty_lift hn hdim i₀).some
  | i + 1 => mkBridge hn hdim
      ((bridgeSeq hn hdim i₀ hsmall i).next hn hdim (hsmall _ (Nat.le_add_right _ _)))

/-- A program with infinitely many birational steps that are all small from `i₀` on cannot
exist: concatenating its bridges gives an infinite elementary dlt program. -/
private theorem false_of_isSmallMorphism (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4)
    (i₀ : ℕ) (hsmall : ∀ i, i₀ ≤ i → IsSmallMorphism (modelStr sX P.sY i) (P.sZ i) (P.f i)) :
    False := by
  let b := bridgeSeq hn hdim i₀ hsmall
  refine not_bridges (fun i => (b i).Q.n.toNat) (fun i => ?_)
    (fun i k => progStep (b i).Q.toElementaryDltProgram k) (fun i k hk => ?_) (fun i k => rfl)
    (fun i => ?_) ((b 0).L.dim (dim_modelSeq P hn hdim _))
  · have h1 := (b i).n_ne_zero
    have h2 := (b i).Q.n_ne_top
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [ENat.toNat_eq_zero] at h
    tauto
  · refine progStep_isStep _ ?_
    rw [← ENat.coe_toNat (b i).Q.n_ne_top]
    exact_mod_cast hk
  · exact DltModel.mk_eq_mk
      ((b i).next_comp hn hdim (hsmall _ (Nat.le_add_right _ _))).symm

/-- The step sequence of a program with infinitely many birational steps. -/
private noncomputable def toStepSequence (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) :
    StepSequence where
  X := modelSeq X P.Y
  sX := modelStr sX P.sY
  K := divisorSeq K P.KY
  B := divisorSeq B P.BY
  Z := P.Z
  sZ := P.sZ
  f := P.f
  fp := P.fp
  isFourfoldStepDiagram i :=
    (P.isPermittedStep i (lt_n P hn i)).isFourfoldStepDiagram (dim_modelSeq P hn hdim i)
  K_eq i := P.KY_eq i (lt_n P hn i)
  B_eq i := P.BY_eq i (lt_n P hn i)

/-- Only finitely many steps of a program lose a prime divisor, so from some index on every
contraction of the program is small. -/
private theorem exists_isSmallMorphism (hn : P.n = ⊤) (hdim : topologicalKrullDim X = 4) :
    ∃ i₀, ∀ i, i₀ ≤ i → IsSmallMorphism (modelStr sX P.sY i) (P.sZ i) (P.f i) := by
  let S := toStepSequence hn hdim
  obtain ⟨i₀, hi₀⟩ := S.finite_setOf_exists_primeDivisor_isExceptionalValuation.bddAbove
  refine ⟨i₀ + 1, fun i hi => ?_⟩
  by_contra hns
  obtain ⟨E, v, hv, hcomap⟩ :=
    (S.isFourfoldStepDiagram i).exists_isExceptionalValuation_of_not_isSmallMorphism hns
  have := hi₀ (Set.mem_setOf.mpr ⟨E, v, hcomap, hv⟩)
  omega

end Lift

/-- **Termination for lc fourfolds over `ℂ`.** Every program from a projective lc fourfold pair
`(X, B)` over `ℂ` with rational boundary has finitely many birational steps. -/
private theorem solution {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hdim : topologicalKrullDim X = 4) (P : Program sX K B) : P.n ≠ ⊤ := by
  intro hn
  obtain ⟨i₀, hsmall⟩ := exists_isSmallMorphism hn hdim
  exact false_of_isSmallMorphism hn hdim i₀ hsmall

end Proof_prop_oai4_lc_lift

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Termination for lc fourfolds over `ℂ`.** Every program from a projective lc fourfold pair
`(X, B)` over `ℂ` with rational boundary has finitely many birational steps: its number of
birational steps `P.n` is not `⊤`. -/
@[mmp "prop_oai4_lc_lift"]
public theorem Program.n_ne_top {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hdim : topologicalKrullDim X = 4) (P : Program sX K B) : P.n ≠ ⊤ :=
      by revert X sX K B hdim P; first | exact Proof_prop_oai4_lc_lift.solution | exact Proof_prop_oai4_lc_lift.solution _ | exact Proof_prop_oai4_lc_lift.solution _ _ | exact Proof_prop_oai4_lc_lift.solution _ _ _ | exact Proof_prop_oai4_lc_lift.solution _ _ _ _

end MMP.Fourfold

