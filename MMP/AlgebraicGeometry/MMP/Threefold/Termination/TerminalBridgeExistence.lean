module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.BridgeProgram
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.CrepantJunctionExistence
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.LowDiscrepancyJunction
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction

/-!
# Terminal bridges exist

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail with common low-discrepancy set
`I_∞`, and let `(p_i, Θ_i)` be a crepant junction of `(X_i, B_i)` extracting `I_∞`. Then there
are a crepant junction `(p_{i+1}, Θ_{i+1})` of `(X_{i+1}, B_{i+1})` extracting `I_∞` and a
terminal bridge from `(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`. Iterating this from a junction of
`(X_0, B_0)` produces a terminal chain over the tail.

## Main results

* `MMP.Fourfold.StabilizedTail.exists_terminalBridge`: every crepant junction of `(X_i, B_i)`
  extracting `I_∞` admits a terminal bridge to some crepant junction of `(X_{i+1}, B_{i+1})`
  extracting `I_∞`.

## Implementation notes

A junction of `(X_i, B_i)` *extracting `I_∞`* is one extracting a finite set `I` of valuations
of `k(X_i)` with `I = I(X_i, B_i)`. For the next junction this condition, `I' = I(X_{i+1},
B_{i+1})`, is the field `MMP.Fourfold.StabilizedTail.TerminalBridge.coe_target` of the bridge, so
the conclusion is the existence of `I'`, the junction and a bridge.
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Mori

namespace Proof_lem_mmp_indexc_bridge_exists

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section PartialIso

/-- Restricting the source of a partial isomorphism restricts its underlying morphism. -/
private theorem restrictSource_hom_ι {X Y : Scheme.{0}} (f : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').iso.hom ≫ (f.restrictSource U hU hU').target.ι =
      X.homOfLE hU' ≫ f.iso.hom ≫ f.target.ι := by
  have h : (Scheme.Opens.isoOfLE hU').inv ≫ (f.source.ι ⁻¹ᵁ U).ι = X.homOfLE hU' := by
    rw [← cancel_mono f.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι,
      Scheme.homOfLE_ι]
  simp [Scheme.PartialIso.restrictSource, reassoc_of% h]

/-- If `e : X ⤏ Y` lies over `a : X ⟶ S` and `b : Y ⟶ S`, then for every partial isomorphism
`c : W ⤏ X`, `b ∘ (e ∘ c) = a ∘ c` as rational maps. -/
private theorem compHom_trans {W X Y S : Scheme.{0}} (c : W.PartialIso X) (e : X.PartialIso Y)
    {a : X ⟶ S} {b : Y ⟶ S} (he : e.IsOver a b) :
    (c.trans e).toRationalMap.compHom b = c.toRationalMap.compHom a := by
  have hU : Dense ((c.target ⊓ e.source : X.Opens) : Set X) :=
    c.dense_target.inter_of_isOpen_right e.dense_source e.source.2
  let r := c.symm.restrictSource _ hU inf_le_left
  let e' := e.restrictSource _ hU inf_le_right
  have hrt : r.target ≤ c.source := Scheme.Opens.ι_image_le _ _
  have hrc : r.source ≤ c.target := inf_le_left
  have key1 : r.iso.hom ≫ W.homOfLE hrt = X.homOfLE hrc ≫ c.iso.inv := by
    rw [← cancel_mono c.source.ι, Category.assoc, Scheme.homOfLE_ι, Category.assoc]
    exact restrictSource_hom_ι c.symm _ hU inf_le_left
  have key2 : r.iso.inv ≫ r.source.ι = W.homOfLE hrt ≫ c.iso.hom ≫ c.target.ι := by
    rw [← cancel_epi r.iso.hom, Iso.hom_inv_id_assoc, reassoc_of% key1, Iso.inv_hom_id_assoc,
      Scheme.homOfLE_ι]
  have he' : e'.iso.hom ≫ e'.target.ι ≫ b = e'.source.ι ≫ a :=
    he.restrictSource _ hU inf_le_right
  have h3 : (c.trans e).iso.hom ≫ (c.trans e).target.ι ≫ b = r.iso.inv ≫ r.source.ι ≫ a := by
    change r.iso.inv ≫ (X.isoOfEq (U := r.source) (V := e'.source) rfl).hom ≫ e'.iso.hom ≫
      e'.target.ι ≫ b = _
    erw [he', Scheme.isoOfEq_hom_ι_assoc]
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨(c.trans e).source, (c.trans e).dense_source, le_rfl, hrt, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom, Scheme.PartialIso.toPartialMap,
    Category.assoc, Scheme.homOfLE_rfl, Category.id_comp]
  rw [h3, reassoc_of% key2]
  rfl

end PartialIso

section Truncation

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} {K : Divisor V} {Θ : QDivisor V}
  (P : RelativeThreefoldProgram sV sZ π K Θ)

/-- The models of the truncation: `V_{min (k + 1) m}`. -/
private abbrev truncY (k : ℕ) : Scheme.{0} := modelSeq V P.Y (min (k + 1) P.m)

/-- The bases of the truncation: `T_k` for `k < m`, then `V_m`. -/
private noncomputable def truncT (k : ℕ) : Scheme.{0} :=
  if k < P.m then P.T k else modelSeq V P.Y P.m

private theorem truncT_of_lt {k : ℕ} (h : k < P.m) : truncT P k = P.T k := if_pos h

private theorem truncT_of_le {k : ℕ} (h : P.m ≤ k) : truncT P k = modelSeq V P.Y P.m :=
  if_neg (not_lt.2 h)

private theorem modelSeq_truncY (k : ℕ) : modelSeq V (truncY P) k = modelSeq V P.Y (min k P.m) := by
  cases k <;> rfl

private theorem modelSeq_truncY_of_le {k : ℕ} (h : k ≤ P.m) :
    modelSeq V (truncY P) k = modelSeq V P.Y k := by
  rw [modelSeq_truncY, min_eq_left h]

private theorem modelSeq_truncY_of_ge {k : ℕ} (h : P.m ≤ k) :
    modelSeq V (truncY P) k = modelSeq V P.Y P.m := by
  rw [modelSeq_truncY, min_eq_right h]

private theorem truncY_of_lt {k : ℕ} (h : k < P.m) : truncY P k = P.Y k := by
  simp only [truncY]
  rw [min_eq_left h]
  rfl

private theorem truncY_of_le {k : ℕ} (h : P.m ≤ k) : truncY P k = modelSeq V P.Y P.m := by
  simp only [truncY]
  rw [min_eq_right (by omega)]

/-- The structure morphisms of the models of the truncation. -/
private noncomputable abbrev truncSY (k : ℕ) : truncY P k ⟶ Spec (.of ℂ) :=
  modelStr sV P.sY (min (k + 1) P.m)

/-- The canonical divisors of the models of the truncation. -/
private abbrev truncKY (k : ℕ) : Divisor (truncY P k) := divisorSeq K P.KY (min (k + 1) P.m)

/-- The boundaries of the models of the truncation. -/
private abbrev truncΘY (k : ℕ) : QDivisor (truncY P k) := divisorSeq Θ P.ΘY (min (k + 1) P.m)

/-- The morphisms to the base of the models of the truncation. -/
private abbrev truncπY (k : ℕ) : truncY P k ⟶ Z := modelMap π P.πY (min (k + 1) P.m)

/-- The structure morphisms of the bases of the truncation. -/
private noncomputable def truncST (k : ℕ) : truncT P k ⟶ Spec (.of ℂ) :=
  if h : k < P.m then eqToHom (truncT_of_lt P h) ≫ P.sT k
  else eqToHom (truncT_of_le P (not_lt.1 h)) ≫ modelStr sV P.sY P.m

/-- The contractions `g_k` of the truncation. -/
private noncomputable def truncG (k : ℕ) : modelSeq V (truncY P) k ⟶ truncT P k :=
  if h : k < P.m then
    eqToHom (modelSeq_truncY_of_le P h.le) ≫ P.g k ≫ eqToHom (truncT_of_lt P h).symm
  else eqToHom (modelSeq_truncY_of_ge P (not_lt.1 h)) ≫ eqToHom (truncT_of_le P (not_lt.1 h)).symm

/-- The morphisms `g_k⁺` of the truncation. -/
private noncomputable def truncGP (k : ℕ) : truncY P k ⟶ truncT P k :=
  if h : k < P.m then eqToHom (truncY_of_lt P h) ≫ P.gp k ≫ eqToHom (truncT_of_lt P h).symm
  else eqToHom (truncY_of_le P (not_lt.1 h)) ≫ eqToHom (truncT_of_le P (not_lt.1 h)).symm

/-- The morphisms `h_k` of the truncation. -/
private noncomputable def truncH (k : ℕ) : truncT P k ⟶ Z :=
  if h : k < P.m then eqToHom (truncT_of_lt P h) ≫ P.h k
  else eqToHom (truncT_of_le P (not_lt.1 h)) ≫ modelMap π P.πY P.m

/-- The extremal rays of the truncation. -/
private def truncR : ∀ k, Set (NumericalCurveClasses (modelStr sV (truncSY P) k))
  | 0 => P.R 0
  | j + 1 => P.R (min (j + 1) P.m)

/-! #### Comparison with the original programme -/

private theorem modelStr_eq_of_eq {a b : ℕ} (hab : a = b)
    (e : modelSeq V P.Y a = modelSeq V P.Y b) :
    modelStr sV P.sY a = eqToHom e ≫ modelStr sV P.sY b := by
  subst hab
  simp

private theorem modelMap_eq_of_eq {a b : ℕ} (hab : a = b)
    (e : modelSeq V P.Y a = modelSeq V P.Y b) :
    modelMap π P.πY a = eqToHom e ≫ modelMap π P.πY b := by
  subst hab
  simp

private theorem heq_divisorSeq_of_eq {R : Type*} [Zero R] (D : DivisorWithCoeffs R V)
    (E : ∀ k, DivisorWithCoeffs R (P.Y k)) {a b : ℕ} (hab : a = b) :
    HEq (divisorSeq D E a) (divisorSeq D E b) := by
  subst hab
  rfl

private theorem heq_R_of_eq {a b : ℕ} (hab : a = b) : HEq (P.R a) (P.R b) := by
  subst hab
  rfl

private theorem modelStr_truncSY {k : ℕ} (hk : k ≤ P.m) :
    modelStr sV (truncSY P) k = eqToHom (modelSeq_truncY_of_le P hk) ≫ modelStr sV P.sY k := by
  cases k with
  | zero => exact (Category.id_comp sV).symm
  | succ j => exact modelStr_eq_of_eq P (min_eq_left hk) _

private theorem modelMap_truncπY {k : ℕ} (hk : k ≤ P.m) :
    modelMap π (truncπY P) k = eqToHom (modelSeq_truncY_of_le P hk) ≫ modelMap π P.πY k := by
  cases k with
  | zero => exact (Category.id_comp π).symm
  | succ j => exact modelMap_eq_of_eq P (min_eq_left hk) _

private theorem heq_divisorSeq_truncKY {k : ℕ} (hk : k ≤ P.m) :
    HEq (divisorSeq K (truncKY P) k) (divisorSeq K P.KY k) := by
  cases k with
  | zero => rfl
  | succ j => exact heq_divisorSeq_of_eq P K P.KY (min_eq_left hk)

private theorem heq_divisorSeq_truncΘY {k : ℕ} (hk : k ≤ P.m) :
    HEq (divisorSeq Θ (truncΘY P) k) (divisorSeq Θ P.ΘY k) := by
  cases k with
  | zero => rfl
  | succ j => exact heq_divisorSeq_of_eq P Θ P.ΘY (min_eq_left hk)

private theorem heq_truncR {k : ℕ} (hk : k ≤ P.m) : HEq (truncR P k) (P.R k) := by
  cases k with
  | zero => rfl
  | succ j => exact heq_R_of_eq P (min_eq_left hk)

private theorem truncST_of_lt {k : ℕ} (hk : k < P.m) :
    truncST P k = eqToHom (truncT_of_lt P hk) ≫ P.sT k := dif_pos hk

private theorem truncG_of_lt {k : ℕ} (hk : k < P.m) :
    truncG P k = eqToHom (modelSeq_truncY_of_le P hk.le) ≫ P.g k ≫
      eqToHom (truncT_of_lt P hk).symm := dif_pos hk

private theorem truncGP_of_lt {k : ℕ} (hk : k < P.m) :
    truncGP P k = eqToHom (truncY_of_lt P hk) ≫ P.gp k ≫ eqToHom (truncT_of_lt P hk).symm :=
  dif_pos hk

private theorem truncH_of_lt {k : ℕ} (hk : k < P.m) :
    truncH P k = eqToHom (truncT_of_lt P hk) ≫ P.h k := dif_pos hk

end Truncation

/-! #### Transport along equalities of schemes -/

section Transport

variable {Z : Scheme.{0}}

/-- A property of a model with its data is invariant under an equality of schemes. -/
private theorem model_transport
    (Φ : ∀ (A : Scheme.{0}) [IsIntegral A] [CompactSpace A] [IsLocallyNoetherian A] [IsNormal A]
      (sA : A ⟶ Spec (.of ℂ)), Set (NumericalCurveClasses sA) → Divisor A → QDivisor A →
        (A ⟶ Z) → Prop)
    {A A' : Scheme.{0}} [IsIntegral A] [CompactSpace A] [IsLocallyNoetherian A] [IsNormal A]
    [IsIntegral A'] [CompactSpace A'] [IsLocallyNoetherian A'] [IsNormal A']
    (eA : A' = A) {sA : A ⟶ Spec (.of ℂ)} {sA' : A' ⟶ Spec (.of ℂ)}
    (hsA : sA' = eqToHom eA ≫ sA) {R : Set (NumericalCurveClasses sA)}
    {R' : Set (NumericalCurveClasses sA')} (hR : HEq R' R) {KA : Divisor A} {KA' : Divisor A'}
    (hKA : HEq KA' KA) {ΘA : QDivisor A} {ΘA' : QDivisor A'} (hΘA : HEq ΘA' ΘA)
    {πA : A ⟶ Z} {πA' : A' ⟶ Z} (hπA : πA' = eqToHom eA ≫ πA)
    (h : Φ A sA R KA ΘA πA) : Φ A' sA' R' KA' ΘA' πA' := by
  subst eA
  simp only [eqToHom_refl, Category.id_comp] at hsA hπA
  subst hsA hπA
  cases hR; cases hKA; cases hΘA
  exact h

/-- A property of a step with its data is invariant under equalities of schemes. -/
private theorem step_transport
    (Φ : ∀ (A B T : Scheme.{0}) [IsIntegral A] [CompactSpace A] [IsLocallyNoetherian A]
      [IsNormal A] [IsIntegral B] [CompactSpace B] [IsLocallyNoetherian B] [IsNormal B]
      (sA : A ⟶ Spec (.of ℂ)), Set (NumericalCurveClasses sA) → (B ⟶ Spec (.of ℂ)) →
        (T ⟶ Spec (.of ℂ)) → Divisor A → QDivisor A → Divisor B → QDivisor B → (A ⟶ Z) →
        (B ⟶ Z) → (A ⟶ T) → (B ⟶ T) → (T ⟶ Z) → Prop)
    {A A' B B' T T' : Scheme.{0}} [IsIntegral A] [CompactSpace A] [IsLocallyNoetherian A]
    [IsNormal A] [IsIntegral A'] [CompactSpace A'] [IsLocallyNoetherian A'] [IsNormal A']
    [IsIntegral B] [CompactSpace B] [IsLocallyNoetherian B] [IsNormal B]
    [IsIntegral B'] [CompactSpace B'] [IsLocallyNoetherian B'] [IsNormal B']
    (eA : A' = A) (eB : B' = B) (eT : T' = T)
    {sA : A ⟶ Spec (.of ℂ)} {sA' : A' ⟶ Spec (.of ℂ)} (hsA : sA' = eqToHom eA ≫ sA)
    {R : Set (NumericalCurveClasses sA)} {R' : Set (NumericalCurveClasses sA')} (hR : HEq R' R)
    {sB : B ⟶ Spec (.of ℂ)} {sB' : B' ⟶ Spec (.of ℂ)} (hsB : sB' = eqToHom eB ≫ sB)
    {sT : T ⟶ Spec (.of ℂ)} {sT' : T' ⟶ Spec (.of ℂ)} (hsT : sT' = eqToHom eT ≫ sT)
    {KA : Divisor A} {KA' : Divisor A'} (hKA : HEq KA' KA)
    {ΘA : QDivisor A} {ΘA' : QDivisor A'} (hΘA : HEq ΘA' ΘA)
    {KB : Divisor B} {KB' : Divisor B'} (hKB : HEq KB' KB)
    {ΘB : QDivisor B} {ΘB' : QDivisor B'} (hΘB : HEq ΘB' ΘB)
    {πA : A ⟶ Z} {πA' : A' ⟶ Z} (hπA : πA' = eqToHom eA ≫ πA)
    {πB : B ⟶ Z} {πB' : B' ⟶ Z} (hπB : πB' = eqToHom eB ≫ πB)
    {g : A ⟶ T} {g' : A' ⟶ T'} (hg : g' = eqToHom eA ≫ g ≫ eqToHom eT.symm)
    {gp : B ⟶ T} {gp' : B' ⟶ T'} (hgp : gp' = eqToHom eB ≫ gp ≫ eqToHom eT.symm)
    {h : T ⟶ Z} {h' : T' ⟶ Z} (hh : h' = eqToHom eT ≫ h)
    (H : Φ A B T sA R sB sT KA ΘA KB ΘB πA πB g gp h) :
    Φ A' B' T' sA' R' sB' sT' KA' ΘA' KB' ΘB' πA' πB' g' gp' h' := by
  subst eA eB eT
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsA hsB hsT hπA hπB hg hgp hh
  subst hsA hsB hsT hπA hπB hg hgp hh
  cases hR; cases hKA; cases hΘA; cases hKB; cases hΘB
  exact H

end Transport

section Truncation

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} {K : Divisor V} {Θ : QDivisor V}
  (P : RelativeThreefoldProgram sV sZ π K Θ)

/-- Every property of a model `V_k`, `k ≤ m`, of a programme with its data holds for the model
`V_k` of the truncation. -/
private theorem truncate_model
    (Φ : ∀ (A : Scheme.{0}) [IsIntegral A] [CompactSpace A] [IsLocallyNoetherian A] [IsNormal A]
      (sA : A ⟶ Spec (.of ℂ)), Set (NumericalCurveClasses sA) → Divisor A → QDivisor A →
        (A ⟶ Z) → Prop)
    {k : ℕ} (hk : k ≤ P.m)
    (H : Φ (modelSeq V P.Y k) (modelStr sV P.sY k) (P.R k) (divisorSeq K P.KY k)
      (divisorSeq Θ P.ΘY k) (modelMap π P.πY k)) :
    Φ (modelSeq V (truncY P) k) (modelStr sV (truncSY P) k) (truncR P k)
      (divisorSeq K (truncKY P) k) (divisorSeq Θ (truncΘY P) k) (modelMap π (truncπY P) k) :=
  model_transport Φ (modelSeq_truncY_of_le P hk) (modelStr_truncSY P hk) (heq_truncR P hk)
    (heq_divisorSeq_truncKY P hk) (heq_divisorSeq_truncΘY P hk) (modelMap_truncπY P hk) H

/-- Every property of a step `V_k → T_k ← V_{k+1}`, `k < m`, of a programme with its data holds
for the `k`-th step of the truncation. -/
private theorem truncate_step
    (Φ : ∀ (A B T : Scheme.{0}) [IsIntegral A] [CompactSpace A] [IsLocallyNoetherian A]
      [IsNormal A] [IsIntegral B] [CompactSpace B] [IsLocallyNoetherian B] [IsNormal B]
      (sA : A ⟶ Spec (.of ℂ)), Set (NumericalCurveClasses sA) → (B ⟶ Spec (.of ℂ)) →
        (T ⟶ Spec (.of ℂ)) → Divisor A → QDivisor A → Divisor B → QDivisor B → (A ⟶ Z) →
        (B ⟶ Z) → (A ⟶ T) → (B ⟶ T) → (T ⟶ Z) → Prop)
    {k : ℕ} (hk : k < P.m)
    (H : Φ (modelSeq V P.Y k) (P.Y k) (P.T k) (modelStr sV P.sY k) (P.R k) (P.sY k) (P.sT k)
      (divisorSeq K P.KY k) (divisorSeq Θ P.ΘY k) (P.KY k) (P.ΘY k) (modelMap π P.πY k)
      (P.πY k) (P.g k) (P.gp k) (P.h k)) :
    Φ (modelSeq V (truncY P) k) (truncY P k) (truncT P k) (modelStr sV (truncSY P) k)
      (truncR P k) (truncSY P k) (truncST P k) (divisorSeq K (truncKY P) k)
      (divisorSeq Θ (truncΘY P) k) (truncKY P k) (truncΘY P k) (modelMap π (truncπY P) k)
      (truncπY P k) (truncG P k) (truncGP P k) (truncH P k) :=
  step_transport Φ (modelSeq_truncY_of_le P hk.le) (modelSeq_truncY_of_le P hk)
    (truncT_of_lt P hk) (modelStr_truncSY P hk.le) (heq_truncR P hk.le) (modelStr_truncSY P hk)
    (truncST_of_lt P hk) (heq_divisorSeq_truncKY P hk.le) (heq_divisorSeq_truncΘY P hk.le)
    (heq_divisorSeq_truncKY P hk) (heq_divisorSeq_truncΘY P hk) (modelMap_truncπY P hk.le)
    (modelMap_truncπY P hk) (truncG_of_lt P hk) (truncGP_of_lt P hk) (truncH_of_lt P hk) H

/-- The *truncation* of a finite relative programme: the same steps `k < m`, followed by
identity steps at the end model `V_m`. -/
private noncomputable def truncate : RelativeThreefoldProgram sV sZ π K Θ where
  m := P.m
  Y := truncY P
  sY := truncSY P
  isIntegral k := inferInstanceAs (IsIntegral (modelSeq V P.Y _))
  compactSpace k := inferInstanceAs (CompactSpace (modelSeq V P.Y _))
  isLocallyNoetherian k := inferInstanceAs (IsLocallyNoetherian (modelSeq V P.Y _))
  isNormal k := inferInstanceAs (IsNormal (modelSeq V P.Y _))
  KY := truncKY P
  ΘY := truncΘY P
  πY := truncπY P
  T := truncT P
  sT := truncST P
  g := truncG P
  gp := truncGP P
  h := truncH P
  R := truncR P
  isProjectiveVariety_base := P.isProjectiveVariety_base
  isNormalVariety_base := P.isNormalVariety_base
  isProjectiveVariety := P.isProjectiveVariety
  dim_eq := P.dim_eq
  isKltPair := P.isKltPair
  isCanonicalDivisor := P.isCanonicalDivisor
  comp_eq := P.comp_eq
  isQFactorial k hk :=
    truncate_model P (fun _ _ _ _ _ sA _ _ _ _ => IsQFactorial sA) hk (P.isQFactorial k hk)
  isThreefoldStepDiagram k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ sA _ sB sT KA ΘA _ _ _ _ g gp _ =>
      IsThreefoldStepDiagram sA sT sB KA ΘA g gp) hk (P.isThreefoldStepDiagram k hk)
  KY_eq k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KA _ KB _ _ _ g gp _ =>
      KB = flipTransform g gp KA) hk (P.KY_eq k hk)
  ΘY_eq k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ΘA _ ΘB _ _ g gp _ =>
      ΘB = flipTransform g gp ΘA) hk (P.ΘY_eq k hk)
  comp_eq_base k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ sT _ _ _ _ _ _ _ _ h => h ≫ sZ = sT) hk
      (P.comp_eq_base k hk)
  modelMap_eq k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ πA _ g _ h => πA = g ≫ h) hk
      (P.modelMap_eq k hk)
  πY_eq k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ πB _ gp h => πB = gp ≫ h) hk
      (P.πY_eq k hk)
  isNegativeExtremalRayOf k hk :=
    truncate_model P (fun _ _ _ _ _ sA R KA ΘA _ =>
      IsNegativeExtremalRayOf sA (Divisor.toQDivisor KA + ΘA) R) hk.le
      (P.isNegativeExtremalRayOf k hk)
  exists_ray_eq k hk :=
    truncate_model P (fun _ _ _ _ _ sA R _ _ πA => ∃ C : ProperCurve sA, C.IsContractedBy πA ∧
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}) hk.le
      (P.exists_ray_eq k hk)
  isContractionOfRay k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ sA R _ sT _ _ _ _ _ _ g _ _ =>
      IsContractionOfRay sA sT R g) hk (P.isContractionOfRay k hk)
  relativePicardNumber_eq_one k hk :=
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ sA _ _ _ _ _ _ _ _ _ g _ _ =>
      relativePicardNumberN1 sA g = 1) hk (P.relativePicardNumber_eq_one k hk)

/-- Every step of the truncation of a programme is a pair of birational morphisms: a step
diagram of the programme for `k < m`, a pair of identities afterwards. -/
private theorem isBirationalMorphism_truncate (k : ℕ) :
    IsBirationalMorphism ((truncate P).g k) ∧ IsBirationalMorphism ((truncate P).gp k) := by
  by_cases hk : k < P.m
  · have h := (truncate P).isThreefoldStepDiagram k hk
    exact ⟨h.isBirationalMorphism_minus, h.isSmallMorphism_plus.isBirationalMorphism⟩
  · change IsBirationalMorphism (truncG P k) ∧ IsBirationalMorphism (truncGP P k)
    rw [truncG, truncGP, dif_neg hk, dif_neg hk]
    exact ⟨isBirationalMorphism_of_isIso _, isBirationalMorphism_of_isIso _⟩

end Truncation

/-! ### The composite birational maps of a programme -/

section Composite

variable {V Z : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
  {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} {K : Divisor V} {Θ : QDivisor V}
  (P : RelativeThreefoldProgram sV sZ π K Θ)
  (hb : ∀ k, IsBirationalMorphism (P.g k) ∧ IsBirationalMorphism (P.gp k))

/-- The birational map `(g_k⁺)⁻¹ ∘ g_k : V_k ⤏ V_{k+1}` as a partial isomorphism. -/
private noncomputable def flipIso (k : ℕ) : (modelSeq V P.Y k).PartialIso (P.Y k) :=
  (hb k).1.choose.trans (hb k).2.choose.symm

/-- The composite `ψ_k : V_0 ⤏ V_k` of the first `k` steps, as a partial isomorphism. -/
private noncomputable def compIso : ∀ k, V.PartialIso (modelSeq V P.Y k)
  | 0 => Scheme.PartialIso.refl V
  | k + 1 => (compIso k).trans (flipIso P hb k)

private theorem flipIso_isOver (k : ℕ) {S : Scheme.{0}} (u : P.T k ⟶ S)
    [IsSeparated (S ↘ ⊤_ Scheme)] : (flipIso P hb k).IsOver (P.g k ≫ u) (P.gp k ≫ u) :=
  (MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq _ _ u (hb k).1.choose_spec).trans
    (MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq _ _ u (hb k).2.choose_spec).symm

private theorem compHom_compIso_succ (k : ℕ) [IsSeparated (P.T k ↘ ⊤_ Scheme)] :
    (compIso P hb (k + 1)).toRationalMap.compHom (P.gp k) =
      (compIso P hb k).toRationalMap.compHom (P.g k) := by
  have h := flipIso_isOver P hb k (𝟙 _)
  rw [Category.comp_id, Category.comp_id] at h
  exact compHom_trans _ _ h

private theorem compIso_isOver [IsSeparated (Z ↘ ⊤_ Scheme)] :
    ∀ k ≤ P.m, (compIso P hb k).IsOver π (modelMap π P.πY k)
  | 0, _ => by
    simp only [compIso, Scheme.PartialIso.IsOver, Scheme.PartialIso.refl_iso, Iso.refl_hom]
    rfl
  | k + 1, hk => by
    have h := flipIso_isOver P hb k (P.h k)
    rw [← P.modelMap_eq k hk, ← P.πY_eq k hk] at h
    exact (compIso_isOver k (Nat.le_of_succ_le hk)).trans h

end Composite

open MMP.Fourfold.Oai4C1 in
private theorem solution : ∀ {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    (J : CrepantJunction (T.sX i) (T.B i) I),
    ∃ (I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))))
      (J' : CrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'),
      Nonempty (StabilizedTail.TerminalBridge i J J') := by
  intro T i I hI J
  have hT := T.isThreefoldStepDiagram i
  -- the finite set `I' = I(X_{i+1}, B_{i+1})`
  have hfin := (T.isKltPair (i + 1)).finite_lowDiscrepancySet
  set I' := hfin.toFinset with hI'def
  have hI' : (I' : Set _) = lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1)) := hfin.coe_toFinset
  -- rational log discrepancies over `(X_{i+1}, B_{i+1})`, from a junction extracting `I'`
  obtain ⟨J''⟩ := CrepantJunction.nonempty (T.isProjectiveVariety (i + 1)) (T.dim_eq (i + 1))
    (fun P => (T.isThreefoldStepDiagram (i + 1)).nonneg P) (T.isKltPair (i + 1)) hI'.le
  obtain ⟨a', ha', -⟩ := J''.Θ_eq
  -- the valuations `s'` of `k(X_{i+1})` corresponding to `s ∈ I`
  have htr : ∀ s : I, ∃ s' ∈ lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1)),
      T.IsTransportedValuation i s s' := by
    intro s
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmem : (s : Valuation _ _) ∈ lowDiscrepancySet (T.sX i) (T.B i) := hI ▸ s.2
    have hs : (s : Valuation _ _).comap (functionFieldMap (T.f i)) ∈
        valuationsOver (T.f i) (lowDiscrepancySet (T.sX i) (T.B i)) := ⟨_, hmem, rfl⟩
    exact (Set.ext_iff.1 (T.lowDiscrepancySet_eq i) _).1 hs
  choose s' hs'mem hs' using htr
  have hs'I : ∀ s, s' s ∈ I' := fun s => by rw [← Finset.mem_coe, hI']; exact hs'mem s
  let a : I → ℚ := fun s => a' ⟨s' s, hs'I s⟩
  set Θ' : QDivisor J.Y :=
    inverseTransformDivisor J.p (T.B i) + ∑ s : I, Finsupp.single (J.E s) (1 - a s) with hΘ'def
  have hΘ' : StabilizedTail.IsDecreasedBoundary J Θ' :=
    ⟨a, fun s => ⟨s' s, hs' s, ha' ⟨s' s, hs'I s⟩⟩, rfl⟩
  -- a canonical divisor `K` of `Y_i` with `(p_i)_* K = K_i`
  have hX : IsNormalVariety ℂ (T.sX i) := hT.isNormalVariety_minus
  have hY : IsNormalVariety ℂ (J.p ≫ T.sX i) := J.isQFactorial.1
  haveI : LocallyOfFiniteType (T.sX i) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (J.p ≫ T.sX i) := hY.1.toLocallyOfFiniteType
  haveI : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  haveI := J.isBirationalMorphism.isDominant
  obtain ⟨n, hKX⟩ := hT.isCanonicalDivisor
  have hdimY : topologicalKrullDim J.Y = n :=
    J.dim_eq.trans ((T.dim_eq i).symm.trans hKX.topologicalKrullDim_eq)
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isNormalVariety (J.p ≫ T.sX i) hY hdimY
  obtain ⟨K, hK, hpK⟩ :=
    Main.exists_isCanonicalDivisor_transformDivisor_eq hX hY J.isBirationalMorphism hKX hK₀
  -- the programme over `Z_i` from `(Y_i, Θ_i')`, made trivial after its end
  obtain ⟨P, hsmall, -, hnef⟩ :=
    StabilizedTail.IsDecreasedBoundary.exists_relativeThreefoldProgram hI hΘ' K ⟨n, hK⟩
  set P' := truncate P with hP'
  have hsmall' : ∀ k < P'.m,
      IsSmallMorphism (modelStr (J.p ≫ T.sX i) P'.sY k) (P'.sT k) (P'.g k) := fun k hk =>
    truncate_step P (fun _ _ _ _ _ _ _ _ _ _ _ sA _ _ sT _ _ _ _ _ _ g _ _ =>
      IsSmallMorphism sA sT g) hk (hsmall k hk)
  have hnef' : QDivisor.IsRelativelyNef (modelStr (J.p ≫ T.sX i) P'.sY P'.m)
      (modelMap (J.p ≫ T.f i) P'.πY P'.m)
      (Divisor.toQDivisor (divisorSeq K P'.KY P'.m) + P'.boundary P'.m) :=
    truncate_model P (fun _ _ _ _ _ sA _ KA ΘA πA =>
      QDivisor.IsRelativelyNef sA πA (Divisor.toQDivisor KA + ΘA)) le_rfl hnef
  -- its end maps crepantly to `X_{i+1}` and is the next junction
  obtain ⟨p, hp, hpb, hcomp, hpull⟩ :=
    StabilizedTail.IsDecreasedBoundary.exists_comp_eq_modelMap_and_isPullback hI hΘ' hpK P' hnef'
  obtain ⟨J', e, he, hbd⟩ :=
    StabilizedTail.IsDecreasedBoundary.exists_crepantJunction_of_isPullback hI hΘ' hpK P' hnef'
      p hp hpb hcomp hpull hI'
  have hb := isBirationalMorphism_truncate P
  haveI : IsSeparated (T.Z i ↘ ⊤_ Scheme) :=
    MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hT.isNormalVariety_target
  refine ⟨I', J', ⟨{
    coe_source := hI
    coe_target := hI'
    K := K
    Θ' := Θ'
    isDecreasedBoundary := hΘ'
    P := P'
    isSmallMorphism := hsmall'
    e := e
    boundary_eq := hbd
    modelMap_eq := by rw [← hcomp, ← he, Category.assoc]
    ψ := fun k => (compIso P' hb k).toRationalMap
    ψ_zero := rfl
    ψ_succ := fun k hk => by
      haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety
        (P'.isThreefoldStepDiagram k hk).isNormalVariety_target
      exact compHom_compIso_succ P' hb k
    compHom_eq := by
      rw [Main.compHom_compHom, Main.compHom_compHom, ← Category.assoc, he, hcomp]
      exact CommonModel.compHom_toRationalMap_of_isOver _ (compIso_isOver P' hb P'.m le_rfl) }⟩⟩

end Proof_lem_mmp_indexc_bridge_exists

end

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedTail

/-- **Terminal bridges exist.** Let `(p_i, Θ_i)` be a crepant junction of `(X_i, B_i)` extracting
`I_∞`, that is, extracting `I = I(X_i, B_i)`. Then there are a finite set `I'` of valuations of
`k(X_{i+1})`, a crepant junction `(p_{i+1}, Θ_{i+1})` of `(X_{i+1}, B_{i+1})` extracting `I'`,
and a terminal bridge from `(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`; in particular
`I' = I(X_{i+1}, B_{i+1})` (`MMP.Fourfold.StabilizedTail.TerminalBridge.coe_target`). -/
@[mmp "lem_mmp_indexc_bridge_exists"]
public theorem exists_terminalBridge {T : StabilizedTail} {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i))
    (J : CrepantJunction (T.sX i) (T.B i) I) :
    ∃ (I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))))
      (J' : CrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'),
      Nonempty (TerminalBridge i J J') :=
  Proof_lem_mmp_indexc_bridge_exists.solution hI J

end StabilizedTail

end MMP.Fourfold
