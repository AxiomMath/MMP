module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor

/-!
# A complement restricts to every component of the floor of a dlt pair

Let `(M, B_M)` be an effective rational `ℚ`-factorial dlt pair, projective over `g : M ⟶ Z`,
and let `A_M ≥ 0` be a `ℚ`-Cartier `ℚ`-divisor such that `(M, B_M + A_M)` is log canonical and
`K_M + B_M + A_M ∼_ℚ g^*H` for a `ℚ`-Cartier `ℚ`-divisor `H` on `Z`. For a prime component `S`
of `⌊B_M⌋`, with the boundary `B_S = Diff_S(B_M - S)` of dlt adjunction, `S` is not contained in
`Supp A_M`, the restriction `A_S = A_M|_S` is an effective `ℚ`-Cartier `ℚ`-divisor,
`(S, B_S + A_S)` is log canonical and `K_S + B_S + A_S ∼_ℚ (g|_S)^*H`. Nothing is claimed about
ampleness or bigness on `S`.

Write `P` for the prime divisor of `M` that `S` normalises. The coefficient of `P` in `B` is
one, so log canonicity of `(M, B + A)` at the divisor `P`
forces `coeff_P A = 0`. Fix a rational top form `τ` with a simple pole along `P` and its
Poincaré residue `ρ`. The different `B_S` is the residue different,
`div ρ + B_S = (div τ + B)|_S`, which is effective; adding `A_S = A|_S` gives
`div ρ + B_S + A_S = (div τ + P + (B - P + A))|_S`. Forward adjunction realises every divisor
over `S` by an exceptional divisor over `M` with the same discrepancy with respect to
`(M, B + A)`, so `(S, B_S + A_S)` is log canonical. Restricting the `ℚ`-linear equivalence
`div τ + B + A ∼_ℚ g^*H` to `S` gives the last assertion.

## Main results

* `MMP.Fourfold.IsAdjunctionStep.exists_isLogCanonicalPair_add_pullback`.

## Implementation notes

The restriction `A_M|_S` is the pull-back `MMP.Mori.QDivisor.pullback` along the inclusion
`j : S ⟶ M`, which is defined because `S ⊄ Supp A_M`; this support condition is part of the
conclusion. The pull-back `g^*H` is the same construction along `g`, so `Z` is taken locally
Noetherian and normal and `H` is required not to contain the image of the generic point of `M`.
Since `(g|_S)^*H` is meaningful only up to `ℚ`-linear equivalence when `g(S) ⊆ Supp H`, the last
assertion is stated for every `ℚ`-Cartier `H' ∼_ℚ H` on `Z` whose support does not contain
`g(S)`, and for every canonical divisor `K_S` of `S`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998]
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6, 17.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Pull-backs of `ℚ`-divisors along arbitrary morphisms -/

section Pullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- The pull-back predicate only depends on the `ℚ`-divisor, not on the proof of `(∗)`. -/
private theorem isPullback_congr {f : X ⟶ Y} {D D' : QDivisor Y} (e : D = D')
    {hD : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    (hD' : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D'.supp)
    {E E' : QDivisor X} (h : D.IsPullback f hD E) (e' : E = E') : D'.IsPullback f hD' E' := by
  subst e e'
  exact h

omit [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- If `G = cΔ` with `c ≠ 0`, then `G` satisfies `(∗)` as soon as `Δ` does. -/
private theorem notMem_supp_of_toQDivisor_eq (f : X ⟶ Y) {G : Divisor Y} {Δ : QDivisor Y}
    {c : ℤ} (hc : c ≠ 0) (h : Divisor.toQDivisor G = c • Δ)
    (hΔ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ Δ.supp) :
    ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ G.supp := by
  intro Z
  rw [QDivisor.supp_eq_of_toQDivisor_eq hc h]
  exact hΔ Z

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- `Supp (D₁ - D₂) ⊆ Supp D₁ ∪ Supp D₂`. -/
private theorem notMem_supp_sub {D₁ D₂ : QDivisor Y} {y : Y} (h₁ : y ∉ D₁.supp)
    (h₂ : y ∉ D₂.supp) : y ∉ (D₁ - D₂).supp := fun h => by
  rw [sub_eq_add_neg] at h
  rcases DivisorWithCoeffs.supp_add_le _ _ h with h | h
  · exact h₁ h
  · exact h₂ (by rwa [DivisorWithCoeffs.supp_neg] at h)

/-- **Effectivity of pull-backs.** The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is
effective. -/
private theorem nonneg_of_isPullback (f : X ⟶ Y) {D : QDivisor Y} (hD0 : 0 ≤ D)
    (hDq : D.IsQCartier)
    {hD : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {D' : QDivisor X} (h : D.IsPullback f hD D') : 0 ≤ D' := by
  obtain ⟨m, hm, G, hG, hGc⟩ := hDq.exists_pos
  obtain ⟨G', hG', hp⟩ := h m hm G hG hGc
  have hGnn : ∀ E, 0 ≤ G.coeff E := fun E => by
    have h1 := congrArg (fun F : QDivisor Y => F.coeff E) hG
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
    have h2 : (0 : ℚ) ≤ D.coeff E := hD0 E
    have : (0 : ℚ) ≤ (G.coeff E : ℚ) := by rw [h1]; positivity
    exact_mod_cast this
  intro Q
  obtain ⟨U, hU, φ, hφ⟩ := hGc (f Q.genericPoint)
  have hE : (Q.support ∩ f ⁻¹ᵁ U).Nonempty := (Q.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  have hc := hp U φ hφ Q hE
  have hnn := MMP.CyclicChartDifferent.ordUnit_pullbackComponent_nonneg f Q hGnn hU hφ
    (notMem_supp_of_toQDivisor_eq f (by exact_mod_cast hm.ne') hG hD)
    (Q.map_componentGenericPoint_mem f hE)
  have h1 := congrArg (fun F : QDivisor X => F.coeff Q) hG'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
  have h2 : (0 : ℚ) ≤ (G'.coeff Q : ℚ) := by rw [hc]; exact_mod_cast hnn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  change (0 : ℚ) ≤ D'.coeff Q
  rw [h1] at h2
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using h2) hm'

/-- **Additivity of the pull-back** of `ℚ`-Cartier `ℚ`-divisors, along an arbitrary morphism
satisfying `(∗)` for both summands and their sum. -/
private theorem isPullback_add [CompactSpace X] (f : X ⟶ Y) {D E : QDivisor Y}
    (hDq : D.IsQCartier) (hEq : E.IsQCartier)
    {hD : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {hE : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ E.supp}
    (hDE : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (D + E).supp)
    {D' E' : QDivisor X} (h₁ : D.IsPullback f hD D') (h₂ : E.IsPullback f hE E') :
    (D + E).IsPullback f hDE (D' + E') := by
  have hF := QDivisor.isPullback_pullback (hDq.add hEq) hDE
  suffices hFeq : (D + E).pullback (hDq.add hEq) hDE = D' + E' by rwa [← hFeq]
  obtain ⟨a, ha, G₁, hG₁, hG₁c⟩ := hDq.exists_pos
  obtain ⟨b, hb, G₂, hG₂, hG₂c⟩ := hEq.exists_pos
  obtain ⟨G₁', hG₁', q₁⟩ := h₁ a ha G₁ hG₁ hG₁c
  obtain ⟨G₂', hG₂', q₂⟩ := h₂ b hb G₂ hG₂ hG₂c
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hG : Divisor.toQDivisor ((b : ℤ) • G₁ + (a : ℤ) • G₂) = ((a * b : ℕ) : ℤ) • (D + E) := by
    rw [map_add, map_zsmul, map_zsmul, hG₁, hG₂, smul_smul, smul_smul, smul_add]
    push_cast
    rw [mul_comm (b : ℤ) a]
  have hGc : ((b : ℤ) • G₁ + (a : ℤ) • G₂).IsCartier := (hG₁c.zsmul _).add (hG₂c.zsmul _)
  obtain ⟨F₀, hF₀, qF⟩ := hF (a * b) (Nat.mul_pos ha hb) _ hG hGc
  have s₁ := notMem_supp_of_toQDivisor_eq f (c := (b : ℤ) * a) (Δ := D) (G := (b : ℤ) • G₁)
    (mul_ne_zero hb' ha') (by rw [map_zsmul, hG₁, smul_smul]) hD
  have s₂ := notMem_supp_of_toQDivisor_eq f (c := (a : ℤ) * b) (Δ := E) (G := (a : ℤ) • G₂)
    (mul_ne_zero ha' hb') (by rw [map_zsmul, hG₂, smul_smul]) hE
  have sG := notMem_supp_of_toQDivisor_eq f (by exact_mod_cast (Nat.mul_pos ha hb).ne') hG hDE
  have r := (q₁.zsmul hG₁c b s₁).add (hG₁c.zsmul _) (hG₂c.zsmul _) sG (q₂.zsmul hG₂c a s₂)
  have e := qF.eq hGc r
  have e2 := congrArg Divisor.toQDivisor e
  rw [hF₀, map_add, map_zsmul, map_zsmul, hG₁', hG₂', smul_smul, smul_smul] at e2
  ext Q
  have e3 := congrArg (fun F : QDivisor X => F.coeff Q) e2
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul] at e3
  push_cast at e3
  rw [DivisorWithCoeffs.coeff_add]
  have hab : ((a : ℚ) * b) ≠ 0 := by positivity
  apply mul_left_cancel₀ hab
  linear_combination e3

/-- **Pull-backs respect `ℚ`-linear equivalence**: pull-backs of `ℚ`-linearly equivalent
`ℚ`-Cartier `ℚ`-divisors are `ℚ`-linearly equivalent. -/
private theorem qLinearlyEquivalent_of_isPullback [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y)
    {D₁ D₂ : QDivisor Y} (h₁q : D₁.IsQCartier) (h₂q : D₂.IsQCartier)
    {h₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₁.supp}
    {h₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D₂.supp}
    {D₁' D₂' : QDivisor X} (p₁ : D₁.IsPullback f h₁ D₁') (p₂ : D₂.IsPullback f h₂ D₂')
    (h : D₁.QLinearlyEquivalent D₂) : D₁'.QLinearlyEquivalent D₂' := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  obtain ⟨a, ha, G₁, hG₁, hG₁c⟩ := h₁q.exists_pos
  obtain ⟨b, hb, G₂, hG₂, hG₂c⟩ := h₂q.exists_pos
  obtain ⟨G₁', hG₁', q₁⟩ := p₁ a ha G₁ hG₁ hG₁c
  obtain ⟨G₂', hG₂', q₂⟩ := p₂ b hb G₂ hG₂ hG₂c
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have key : ((m : ℤ) * b) • G₁ = ((m : ℤ) * a) • G₂ + ((a : ℤ) * b) • principalDivisor φ := by
    apply Divisor.toQDivisor_injective
    rw [map_add, map_zsmul, map_zsmul, map_zsmul, hG₁, hG₂, ← hφ, smul_smul, smul_smul,
      smul_smul, smul_sub]
    ext E
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, zsmul_eq_mul]
    push_cast
    ring
  have hφs : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (principalDivisor φ).supp :=
    notMem_supp_of_toQDivisor_eq f hm' hφ.symm fun Z => notMem_supp_sub (h₁ Z) (h₂ Z)
  have pφ := Divisor.isPullback_principalDivisor (f := f) φ hφs
  have s₁ := notMem_supp_of_toQDivisor_eq f (c := (m : ℤ) * b * a) (Δ := D₁)
    (G := ((m : ℤ) * b) • G₁) (mul_ne_zero (mul_ne_zero hm' hb') ha')
    (by rw [map_zsmul, hG₁, smul_smul]) h₁
  have s₂ := notMem_supp_of_toQDivisor_eq f (c := (m : ℤ) * a * b) (Δ := D₂)
    (G := ((m : ℤ) * a) • G₂) (mul_ne_zero (mul_ne_zero hm' ha') hb')
    (by rw [map_zsmul, hG₂, smul_smul]) h₂
  have s₄ : ∀ Z : irreducibleComponents X,
      f (componentGenericPoint X Z) ∉ (((a : ℤ) * b) • principalDivisor φ).supp :=
    notMem_supp_of_toQDivisor_eq f (c := (a : ℤ) * b) (Δ := Divisor.toQDivisor (principalDivisor φ))
      (mul_ne_zero ha' hb') (by rw [map_zsmul])
      (by simpa only [Divisor.supp_toQDivisor] using hφs)
  have s₃ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉
      (((m : ℤ) * a) • G₂ + ((a : ℤ) * b) • principalDivisor φ).supp := by
    rwa [← key]
  have r₁ := q₁.zsmul hG₁c ((m : ℤ) * b) s₁
  have r₂ := (q₂.zsmul hG₂c ((m : ℤ) * a) s₂).add (hG₂c.zsmul _)
    ((Divisor.isCartier_principalDivisor φ).zsmul _) s₃
    (pφ.zsmul (Divisor.isCartier_principalDivisor φ) ((a : ℤ) * b) s₄)
  have e := r₁.eq (hG₁c.zsmul _) (r₂.of_eq key.symm (hB₂ := s₁))
  refine ⟨m, hm, MMP.Mori.pullbackRationalFunction f φ hφs, ?_⟩
  have e2 := congrArg Divisor.toQDivisor e
  rw [map_add, map_zsmul, map_zsmul, map_zsmul, hG₁', hG₂', smul_smul, smul_smul] at e2
  ext Q
  have e3 := congrArg (fun F : QDivisor X => F.coeff Q) e2
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor] at e3
  push_cast at e3
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, zsmul_eq_mul,
    Divisor.coeff_toQDivisor]
  have hab : ((a : ℚ) * b) ≠ 0 := by positivity
  apply mul_left_cancel₀ hab
  linear_combination e3

/-- A pull-back has coefficient zero along a prime divisor whose generic point is sent off the
support. -/
private theorem coeff_eq_zero_of_isPullback (f : X ⟶ Y) {D : QDivisor Y} (hDq : D.IsQCartier)
    {hD : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {D' : QDivisor X} (h : D.IsPullback f hD D') (Q : MMP.Mori.PrimeDivisor X)
    (hQ : f Q.genericPoint ∉ D.supp) : D'.coeff Q = 0 := by
  obtain ⟨m, hm, G, hG, hGc⟩ := hDq.exists_pos
  obtain ⟨G', hG', hp⟩ := h m hm G hG hGc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hGs : (G.supp : Set Y) = D.supp := by rw [QDivisor.supp_eq_of_toQDivisor_eq hm' hG]
  let U : Y.Opens := ⟨(G.supp : Set Y)ᶜ, G.isClosed_supp.isOpen_compl⟩
  have hU : G.IsLocalEquation U 1 := by
    intro E ⟨y, hyE, hyU⟩
    rw [MMP.Mori.PrimeDivisor.ord_one]
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  have hQU : f Q.genericPoint ∈ U := by
    change f Q.genericPoint ∉ (G.supp : Set Y)
    rwa [hGs]
  have hE : (Q.support ∩ f ⁻¹ᵁ U).Nonempty := (Q.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hQU
  have hc := hp U 1 hU Q hE
  rw [MMP.CyclicChartDifferent.ordUnit_pullbackComponent_one f Q rfl hU _ _] at hc
  have h1 := congrArg (fun F : QDivisor X => F.coeff Q) hG'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, hc,
    Int.cast_zero] at h1
  have hm'' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact (mul_eq_zero.mp h1.symm).resolve_left hm''

end Pullback

/-! ### Pull-backs along composites -/

section Composite

variable {X Y W : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y] [IsLocallyNoetherian W] [IsNormal W]

omit [IsLocallyNoetherian X] in
/-- On a normal scheme a generization of a point lies on the irreducible component of the point:
the components are disjoint. -/
private theorem mem_pointComponent_of_specializes {x y : X} (h : x ⤳ y) :
    x ∈ (pointComponent y).1 := by
  have hy : y ∈ (pointComponent x).1 :=
    h.mem_closed (isClosed_of_mem_irreducibleComponents _ (pointComponent x).2)
      (mem_pointComponent x)
  rw [eq_of_mem_irreducibleComponents (mem_pointComponent y) hy]
  exact mem_pointComponent x

/-- **Pull-back of Cartier divisors along a composite**, for an arbitrary normal target. -/
private theorem divisor_isPullback_comp {f : Y ⟶ X} {g : W ⟶ Y} {L : Divisor X}
    {L' : Divisor Y} {L'' : Divisor W}
    {hB : ∀ V : irreducibleComponents Y, f (componentGenericPoint Y V) ∉ L.supp}
    {hB' : ∀ V : irreducibleComponents W, g (componentGenericPoint W V) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ V : irreducibleComponents W, (g ≫ f) (componentGenericPoint W V) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint W E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_pointComponent ((g ≫ f) z))
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set V := pointComponent (g z)
  have hspec : componentGenericPoint Y V ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y V).specializes (mem_pointComponent _)
  have hfspec := f.base.hom.map_specializes hspec
  have hWU : f (componentGenericPoint Y V) ∈ U := hfspec.mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) V := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ V hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU (mem_pointComponent_of_specializes hfspec)
      (Units.map (X.presheaf.stalkSpecializes hfspec).hom.toMonoidHom a) ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes hfspec).hom a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes hfspec ≫ X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pull-back of `ℚ`-divisors along a composite**, for an arbitrary normal target. -/
private theorem qDivisor_isPullback_comp {f : Y ⟶ X} {g : W ⟶ Y} {L : QDivisor X}
    {L' : QDivisor Y} {L'' : QDivisor W}
    {hB : ∀ V : irreducibleComponents Y, f (componentGenericPoint Y V) ∉ L.supp}
    {hB' : ∀ V : irreducibleComponents W, g (componentGenericPoint W V) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ V : irreducibleComponents W, (g ≫ f) (componentGenericPoint W V) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro m hm D hD hDc
  obtain ⟨D', hD', hpb⟩ := h m hm D hD hDc
  obtain ⟨D'', hD'', hpb'⟩ := h' m hm D' hD' (hpb.isCartier hDc)
  exact ⟨D'', hD'', divisor_isPullback_comp hpb hpb' _⟩

end Composite

/-! ### Divisors on `ℚ`-factorial varieties, and discrepancies of lc pairs -/

/-- On a log canonical pair every Kollár–Mori discrepancy is at least `-1`. -/
private theorem neg_one_le_of_isLogCanonicalPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {Δ : QDivisor X}
    (h : MMP.Intersection.IsLogCanonicalPair sX Δ) {N : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX N) {E : DivisorOver ℂ sX} {a : ℚ}
    (ha : IsDiscrepancy sX N K Δ E a) : -1 ≤ a := by
  obtain ⟨hP, -, hlc⟩ := h
  obtain ⟨E', hE'⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hP.1 E
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E'.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hE'
  have h1 := hlc N _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E'.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE'.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')

/-- The coheight of a point is at most the dimension of the scheme. -/
private theorem coheight_le_topologicalKrullDim {X : Scheme.{0}} {d : ℕ}
    (h : topologicalKrullDim X = d) (x : X) : Order.coheight x ≤ d := by
  have h2 : ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X]
    exact le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, h] at h2
  exact_mod_cast h2

/-- A scheme of dimension zero has no prime divisors. -/
private theorem isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero {X : Scheme.{0}}
    (h : topologicalKrullDim X = (0 : ℕ)) :
    IsEmpty (MMP.Mori.PrimeDivisor X) := by
  refine ⟨fun E => ?_⟩
  have h1 := coheight_le_topologicalKrullDim h E.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h1
  exact absurd h1 (by decide)

/-- `ℚ`-linear equivalence is compatible with adding a `ℚ`-divisor. -/
private theorem qLinearlyEquivalent_add_right {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] {D₁ D₂ : QDivisor X} (h : D₁.QLinearlyEquivalent D₂)
    (E : QDivisor X) : (D₁ + E).QLinearlyEquivalent (D₂ + E) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  exact ⟨m, hm, φ, by rwa [add_sub_add_right_eq_sub]⟩

/-! ### A form with a simple pole and its residue -/

/-- A field of finite type over `ℂ` of transcendence degree `n` has `n` elements with linearly
independent differentials. -/
private theorem exists_linearIndependent_kaehlerDifferential {L : Type} [Field L] [Algebra ℂ L]
    [Algebra.EssFiniteType ℂ L] {n : ℕ} (hn : (Algebra.trdeg ℂ L).toNat = n) :
    ∃ y : Fin n → L, LinearIndependent L fun i => KaehlerDifferential.D ℂ L (y i) := by
  have hK : Module.finrank L Ω[L⁄ℂ] = n := (finrank_kaehlerDifferential_eq_trdeg ℂ L).trans hn
  have : FiniteDimensional L Ω[L⁄ℂ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent ℂ L).1
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent L (Set.range (KaehlerDifferential.D ℂ L))
  have hspan : Submodule.span L b = ⊤ :=
    hbspan.trans (KaehlerDifferential.span_range_derivation ℂ L)
  let bb := Module.Basis.mk hbli (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hspan])
  have : Finite b := Module.Finite.finite_basis bb
  have hcard : Nat.card b = n := by rw [← hK, Module.finrank_eq_nat_card_basis bb]
  let e : Fin n ≃ b := (Finite.equivFinOfCardEq hcard).symm
  choose y hy using fun i : Fin n => hbsub (e i).2
  refine ⟨y, ?_⟩
  rw [show (fun i => KaehlerDifferential.D ℂ L (y i)) = fun i => ((e i : b) : Ω[L⁄ℂ]) from
    funext hy]
  exact hbli.comp e e.injective

/-- **A rational top form with a simple pole along a normal prime divisor, and a nonzero Poincaré
residue of it**, given a prime divisor of the normal prime divisor. -/
private theorem exists_form_isPoincareResidue {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : MMP.Mori.PrimeDivisor T) :
    ∃ τ : RationalPluriForms sX (n + 1) 1, τ ≠ 0 ∧ P.ordForm τ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sX) n 1, IsPoincareResidue sX j n 1 τ ρ ∧ ρ ≠ 0 := by
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  let := stalkAlgebra sX (j (genericPoint T))
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg ℂ X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg ℂ T.functionField).toNat = n := by
    have := MMP.CyclicChartDifferent.Aux.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P
      hjT
    omega
  have := essFiniteType_functionField (sX := j ≫ sX)
  obtain ⟨y, hli⟩ := exists_linearIndependent_kaehlerDifferential hdT
  choose x hx using fun i : Fin n =>
    SurjectiveOnStalks.stalkMap_surjective j (genericPoint T) (y i)
  -- a uniformizer along `P`
  obtain ⟨ϖ, -, hϖ0, -, -, hϖ2, -⟩ := MMP.Fourfold.exists_uniformizer_of_eq_genericPoint
    (sY := sX) (j := j) P hjT
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (genericPoint T))) :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) (RingHom.mem_ker.mpr hϖ0)
  have hϖne : ϖ ≠ 0 := fun h => hϖ2 (h ▸ Submodule.zero_mem _)
  have hϖK : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖne
  -- the form `dϖ/ϖ ∧ dx₁ ∧ ⋯ ∧ dxₙ`
  let ν : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] X.presheaf.stalk (j (genericPoint T)) :=
    MvPolynomial.aeval (Fin.cons ϖ x)
  have hν0 : ν (MvPolynomial.X 0) = ϖ := by simp [ν]
  have hνs : ∀ i : Fin n, ν (MvPolynomial.X i.succ) = x i := fun i => by simp [ν]
  have hliν : LinearIndependent T.functionField (fun i : Fin n =>
      KaehlerDifferential.D ℂ T.functionField
        ((j.stalkMap (genericPoint T)).hom (ν (MvPolynomial.X i.succ)))) := by
    simp only [hνs]
    convert hli using 2 with i
    exact congrArg _ (hx i)
  have hF : (algebraMap _ X.functionField ϖ)⁻¹ * algebraMap _ X.functionField (ν (MvPolynomial.X 0))
      = algebraMap _ X.functionField (1 : X.presheaf.stalk (j (genericPoint T))) := by
    rw [hν0, map_one, inv_mul_cancel₀ hϖK]
  obtain ⟨e', -, hres, hord⟩ := MMP.Fourfold.exists_isPoincareResidue_smul_tprod_ιMulti sX hd j P
    hjT ν (hν0 ▸ hϖm) (hν0 ▸ hϖne) hliν hF
  have hτ := hord isUnit_one
  refine ⟨_, ?_, hτ, _, hres,
    MMP.CyclicChartDifferent.Aux.isPoincareResidue_ne_zero sX hX hdim j hT P hP _ ?_ hτ _ hres
      Q⟩ <;>
  · intro h0
    rw [h0, MMP.Mori.PrimeDivisor.ordForm_zero] at hτ
    exact absurd hτ (by decide)

/-! ### The steps of the restriction -/

/-- Along a prime divisor with coefficient one in `B`, an effective `A` with `(X, B + A)` log
canonical has coefficient zero. -/
private theorem coeff_eq_zero_of_isLogCanonicalPair_add {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {B A : QDivisor X} (hA0 : 0 ≤ A)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A)) {P : MMP.Mori.PrimeDivisor X}
    (hBP : B.coeff P = 1) : A.coeff P = 0 := by
  obtain ⟨n', hn'⟩ := MMP.Fourfold.isLogDiscrepancy_ofPrimeDivisor hlc.1.1 hlc.1 P
  have h1 := hlc.2.2 n' _ _ hn'
  have h2 : 0 ≤ A.coeff P := hA0 P
  have h3 : ((B + A).coeff P : ℝ) ≤ 1 := by linarith
  have h4 : (B + A).coeff P ≤ 1 := by exact_mod_cast h3
  rw [DivisorWithCoeffs.coeff_add, hBP] at h4
  linarith

/-- On a normal variety of dimension zero every `ℚ`-divisor is a log canonical boundary. -/
private theorem isLogCanonicalPair_of_topologicalKrullDim_eq_zero {S : Scheme.{0}}
    {sS : S ⟶ Spec (.of ℂ)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    [LocallyOfFiniteType sS] (hSv : IsNormalVariety ℂ sS)
    (hdimS : topologicalKrullDim S = (0 : ℕ)) (Δ : QDivisor S) :
    MMP.Intersection.IsLogCanonicalPair sS Δ := by
  have := isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero hdimS
  obtain ⟨KS₀, hKS₀⟩ := MMP.Mori.exists_isCanonicalDivisor sS hSv hdimS
  refine ⟨⟨hSv, 0, KS₀, hKS₀, ?_⟩, isEmptyElim, fun n' F a _ => ?_⟩
  · rw [show Divisor.toQDivisor KS₀ + Δ = 0 from Finsupp.ext isEmptyElim]
    exact ⟨1, one_ne_zero, 0, by simp, Divisor.isCartier_zero⟩
  · have h2 := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hSv F).mpr
      isEmptyElim
    rw [MMP.Positivity.DivisorOver.codimension_center] at h2
    exact absurd (h2.trans (coheight_le_topologicalKrullDim hdimS (F.f F.E.genericPoint)))
      (by decide)

/-- Removing a prime divisor of coefficient one from an effective `ℚ`-divisor keeps it
effective. -/
private theorem coeff_sub_single_nonneg {X : Scheme.{0}} {B : QDivisor X}
    (hB : ∀ E, 0 ≤ B.coeff E) {P : MMP.Mori.PrimeDivisor X} (hBP : B.coeff P = 1) (E) :
    0 ≤ (B - Finsupp.single P 1).coeff E := by
  rw [DivisorWithCoeffs.coeff_sub]
  by_cases hE : E = P
  · subst hE
    rw [DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hE), sub_zero]
    exact hB E

/-- **The residue different is effective.** If `div ρ + B_S` is the restriction of `div τ + B`
to the normal prime divisor `S` with `B.coeff P = 1`, where `ρ` is the Poincaré residue of `τ`,
then `B_S ≥ 0`. -/
private theorem coeff_nonneg_of_isPullback_isPoincareResidue {M S : Scheme.{0}}
    {sM : M ⟶ Spec (.of ℂ)} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
    [LocallyOfFiniteType sM] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {n : ℕ} (hdim : topologicalKrullDim M = n + 1) {B : QDivisor M} (hB : IsPair sM B)
    {j : S ⟶ M} [IsClosedImmersion j] (hSv : IsNormalVariety ℂ (j ≫ sM))
    {P : MMP.Mori.PrimeDivisor M} (hrange : Set.range j.base = (P.support : Set M))
    (hBP : B.coeff P = 1) {τ : RationalPluriForms sM (n + 1) 1} (hτ0 : τ ≠ 0)
    (hτ : P.ordForm τ = -1) {ρ : RationalPluriForms (j ≫ sM) n 1}
    (hρ : IsPoincareResidue sM j n 1 τ ρ)
    (hD1q : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier) {BS : QDivisor S}
    {hgen1 : ∀ T : irreducibleComponents S,
      j (componentGenericPoint S T) ∉ (Divisor.toQDivisor (divisorOfForm τ) + B).supp}
    (hpb1 : (Divisor.toQDivisor (divisorOfForm τ) + B).IsPullback j hgen1
      (Divisor.toQDivisor (divisorOfForm ρ) + BS)) (Q' : MMP.Mori.PrimeDivisor S) :
    0 ≤ BS.coeff Q' := by
  set B₀ : QDivisor M := B - Finsupp.single P 1 with hB₀def
  have hB₀P : B₀.coeff P = 0 := by
    rw [hB₀def, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
  have heq1 : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B₀ =
      Divisor.toQDivisor (divisorOfForm τ) + B := by rw [hB₀def]; abel
  have hc1 : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B₀).coeff P = 0 := by
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ,
      DivisorWithCoeffs.coeff_single_self, hB₀P]
    norm_num
  have hgen := MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hrange hc1
  exact MMP.Fourfold.coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue sM hB.isPair.1
    hdim j hSv P hrange B₀ (coeff_sub_single_nonneg hB.nonneg hBP) hB₀P τ hτ0 hτ ρ hρ
    (heq1 ▸ hD1q) BS hgen (isPullback_congr heq1.symm hgen hpb1 rfl) Q'

/-- **Forward adjunction for log canonicity.** If `div ρ + Δ` is the restriction of
`div τ + B + A` to the normal prime divisor `S ≅ P`, where `ρ` is the Poincaré residue of `τ`,
`B.coeff P = 1`, `A.coeff P = 0` and `(M, B + A)` is log canonical, then `(S, Δ)` is log
canonical as soon as `Δ ≥ 0`. -/
private theorem isLogCanonicalPair_of_isPullback_isPoincareResidue {M S : Scheme.{0}}
    {sM : M ⟶ Spec (.of ℂ)} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
    [LocallyOfFiniteType sM] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    (hQ : IsQFactorial sM) {n : ℕ} {K : Divisor M}
    (hK : K.IsCanonicalDivisor sM (n + 1)) (hdim : topologicalKrullDim M = n + 1)
    {j : S ⟶ M} [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ sM)]
    (hSv : IsNormalVariety ℂ (j ≫ sM)) (hdimS : topologicalKrullDim S = n)
    {P : MMP.Mori.PrimeDivisor M} (hrange : Set.range j.base = (P.support : Set M))
    {B A : QDivisor M} (hB : ∀ E, 0 ≤ B.coeff E) (hBP : B.coeff P = 1) (hA0 : 0 ≤ A)
    (hAP : A.coeff P = 0) (hlc : MMP.Intersection.IsLogCanonicalPair sM (B + A))
    {τ : RationalPluriForms sM (n + 1) 1} (hτ0 : τ ≠ 0) {ρ : RationalPluriForms (j ≫ sM) n 1}
    (hρ : IsPoincareResidue sM j n 1 τ ρ) (hρ0 : ρ ≠ 0) {Δ : QDivisor S}
    (hΔ0 : ∀ Q', 0 ≤ Δ.coeff Q') (hDP : (Divisor.toQDivisor (divisorOfForm τ) + B + A).coeff P = 0)
    {hgen : ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + B + A).supp}
    (hpb : (Divisor.toQDivisor (divisorOfForm τ) + B + A).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + Δ)) :
    MMP.Intersection.IsLogCanonicalPair (j ≫ sM) Δ := by
  have hMv : IsNormalVariety ℂ sM := hlc.1.1
  set B' : QDivisor M := B - Finsupp.single P 1 + A with hB'def
  have hB'P : B'.coeff P = 0 := by
    rw [hB'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_single_self, hBP, hAP, sub_self, add_zero]
  have hB'nn : 0 ≤ B' := fun E => add_nonneg (coeff_sub_single_nonneg hB hBP E) (hA0 E)
  have heq2 : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B' =
      Divisor.toQDivisor (divisorOfForm τ) + B + A := by rw [hB'def]; abel
  have hB'A : Finsupp.single P (1 : ℚ) + B' = B + A := by rw [hB'def]; abel
  have hc2 : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B').coeff P = 0 := by
    rwa [heq2]
  have hgen2 := MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hrange hc2
  obtain ⟨m, hm, DM, hDM, hDMc⟩ :=
    (MMP.Fourfold.isQCartier_of_isQFactorial sM hQ
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B')).exists_pos
  obtain ⟨M', rfl⟩ : ∃ M', m = M' + 1 := ⟨m - 1, by omega⟩
  have hgS := MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sM hdim j hSv
    hdimS P hrange B' τ hτ0 ρ hρ hρ0 Δ hgen2 (isPullback_congr heq2.symm hgen2 hpb rfl) M' DM
    hDM hDMc
  obtain ⟨KS₀, hKS₀⟩ := MMP.Mori.exists_isCanonicalDivisor (j ≫ sM) hSv hdimS
  have hCartS := MMP.Fourfold.isCartierDivisor_of_forall_generatesOn hSv hKS₀ (Δ := Δ)
    (m := M' + 1) fun x => by
      obtain ⟨U, hxU, -, -, ρ', -, hρ'⟩ := hgS x
      exact ⟨j ⁻¹ᵁ U, hxU, ρ', hρ'⟩
  have hpairS : MMP.Mori.IsPair (j ≫ sM) Δ :=
    ⟨hSv, n, KS₀, hKS₀, ⟨((M' + 1 : ℕ) : ℤ), by positivity, hCartS⟩⟩
  refine ⟨hpairS, hΔ0, fun n' F a ha => ?_⟩
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpairS hKS₀ F
  have hn' : n' = n := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [hdimS] at this
    exact_mod_cast this.symm
  rw [hn'] at ha
  have hEq := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha' a).mp ha).2
  obtain ⟨E, -, -, hiff⟩ :=
    MMP.Fourfold.exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue sM hMv n K hK P j
      hSv hrange KS₀ hKS₀ B' hB'nn hB'P (MMP.Fourfold.isQCartier_of_isQFactorial sM hQ _).exists_pos
      Δ ⟨M' + 1, by omega, hgS⟩ F
  have hE := (hiff a').mp ha'
  rw [hB'A] at hE
  have h2 : (-1 : ℝ) ≤ a' := by exact_mod_cast neg_one_le_of_isLogCanonicalPair hlc hK hE
  rw [hEq]
  linarith

/-- **Restricting a `ℚ`-linear equivalence to a normal prime divisor.** If `D` restricts to `D_S`
along `j : S ⟶ M` and `D ∼_ℚ g^*H`, then `D_S ∼_ℚ (j ≫ g)^*H'` for every `ℚ`-Cartier
`H' ∼_ℚ H` whose pull-back to `S` is defined. -/
private theorem qLinearlyEquivalent_pullback_of_isPullback {M Z S : Scheme.{0}} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {g : M ⟶ Z} {j : S ⟶ M} {P : MMP.Mori.PrimeDivisor M}
    (hjT : j (genericPoint S) = P.genericPoint)
    (hgen : ∀ {G : QDivisor M}, G.coeff P = 0 →
      ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ G.supp)
    {D : QDivisor M} (hDq : D.IsQCartier)
    {hD : ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ D.supp}
    {DS : QDivisor S} (hpb : D.IsPullback j hD DS) {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgH : ∀ T : irreducibleComponents M, g (componentGenericPoint M T) ∉ H.supp)
    (hlin : D.QLinearlyEquivalent (H.pullback hHq hgH)) (H' : QDivisor Z) (hH'q : H'.IsQCartier)
    (hH' : ∀ T : irreducibleComponents S, (j ≫ g) (componentGenericPoint S T) ∉ H'.supp)
    (hH'H : H'.QLinearlyEquivalent H) : DS.QLinearlyEquivalent (H'.pullback hH'q hH') := by
  set T₀ : irreducibleComponents S := pointComponent (genericPoint S)
  have hT₀ : componentGenericPoint S T₀ = genericPoint S :=
    MMP.Fourfold.componentGenericPoint_eq_genericPoint T₀
  have hgH' : ∀ T : irreducibleComponents M, g (componentGenericPoint M T) ∉ H'.supp := by
    intro T hT
    have hsp : g (componentGenericPoint M T) ⤳ (j ≫ g) (componentGenericPoint S T₀) := by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint T, hT₀]
      exact g.base.hom.map_specializes (genericPoint_specializes _)
    exact hH' T₀ (hsp.mem_closed H'.isClosed_supp hT)
  set GH' := H'.pullback hH'q hgH'
  have hGpb : H'.IsPullback g hgH' GH' := QDivisor.isPullback_pullback hH'q hgH'
  have hGq : GH'.IsQCartier := hGpb.isQCartier hH'q
  have h3 : (H.pullback hHq hgH).QLinearlyEquivalent GH' :=
    qLinearlyEquivalent_of_isPullback g hHq hH'q (QDivisor.isPullback_pullback hHq hgH) hGpb
      hH'H.symm
  have hGP : GH'.coeff P = 0 := by
    refine coeff_eq_zero_of_isPullback g hH'q hGpb P ?_
    have := hH' T₀
    rwa [hT₀, Scheme.Hom.comp_apply, hjT] at this
  have hGSpb := QDivisor.isPullback_pullback hGq (hgen hGP)
  rw [(qDivisor_isPullback_comp hGpb hGSpb hH').pullback_eq hH'q]
  exact qLinearlyEquivalent_of_isPullback j hDq hGq hpb hGSpb (hlin.trans h3)

/-- **The case of positive dimension** of
`IsAdjunctionStep.exists_isLogCanonicalPair_add_pullback`: log canonicity of `(S, B_S + A_S)` and
the linear equivalence, by restricting `div τ + B + A` to `S` for a form `τ` with a simple pole
along `P`. -/
private theorem IsAdjunctionStep.isLogCanonicalPair_add_and_qLinearlyEquivalent
    {M Z S : Scheme.{0}} {sM : M ⟶ Spec (.of ℂ)}
    [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {n : ℕ} (hn : 0 < n) {K : Divisor M} (hK : K.IsCanonicalDivisor sM (n + 1))
    (hdim : topologicalKrullDim M = n + 1) {B A : QDivisor M} (hB : IsPair sM B)
    (hQ : IsQFactorial sM) {g : M ⟶ Z} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sM (B + A)) {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgH : ∀ T : irreducibleComponents M, g (componentGenericPoint M T) ∉ H.supp)
    (hlin : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent (H.pullback hHq hgH))
    {j : S ⟶ M} [IsClosedImmersion j] {BS : QDivisor S} (hS : IsAdjunctionStep sM B j BS)
    (hSv : IsNormalVariety ℂ (j ≫ sM)) (hdimS : topologicalKrullDim S = n)
    {P : MMP.Mori.PrimeDivisor M} (hrange : Set.range j.base = (P.support : Set M))
    (hBP : B.coeff P = 1) (hAP : A.coeff P = 0)
    {hA : ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ A.supp}
    {AS : QDivisor S} (hApb : A.IsPullback j hA AS) (hAS0 : 0 ≤ AS) :
    MMP.Intersection.IsLogCanonicalPair (j ≫ sM) (BS + AS) ∧
      ∀ (KS : Divisor S), KS.IsCanonicalDivisor (j ≫ sM) n →
        ∀ (H' : QDivisor Z) (hH'q : H'.IsQCartier)
          (hH' : ∀ T : irreducibleComponents S, (j ≫ g) (componentGenericPoint S T) ∉ H'.supp),
          H'.QLinearlyEquivalent H →
          (Divisor.toQDivisor KS + BS + AS).QLinearlyEquivalent (H'.pullback hH'q hH') := by
  have hMv : IsNormalVariety ℂ sM := hB.isPair.1
  have : LocallyOfFiniteType (j ≫ sM) := hSv.1.toLocallyOfFiniteType
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimS hn.ne'
  obtain ⟨τ, hτ0, hτ, ρ, hρ, hρ0⟩ := exists_form_isPoincareResidue sM hMv hdim j hSv P hrange Q
  have hD1q : (Divisor.toQDivisor (divisorOfForm τ) + B).IsQCartier :=
    MMP.Fourfold.isQCartier_of_isQFactorial sM hQ _
  obtain ⟨hgen1, hpb1⟩ :=
    hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hrange τ hτ0 hτ ρ hρ hD1q
  have hBS0 := coeff_nonneg_of_isPullback_isPoincareResidue hdim hB hSv hrange hBP hτ0 hτ hρ
    hD1q hpb1
  have hDP : (Divisor.toQDivisor (divisorOfForm τ) + B + A).coeff P = 0 := by
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm, hτ,
      hBP, hAP]
    norm_num
  have hgen : ∀ {G : QDivisor M}, G.coeff P = 0 →
      ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ G.supp := fun hG =>
    MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hrange hG
  have hpbD := isPullback_add j hD1q hAq (hgen hDP) hpb1 hApb
  refine ⟨isLogCanonicalPair_of_isPullback_isPoincareResidue hQ hK hdim hSv hdimS hrange
    hB.nonneg hBP hA0 hAP hlc hτ0 hρ hρ0
    (fun Q' => by rw [DivisorWithCoeffs.coeff_add]; exact add_nonneg (hBS0 Q') (hAS0 Q')) hDP
    (isPullback_congr rfl (hgen hDP) hpbD (add_assoc _ _ _)), ?_⟩
  intro KS hKS H' hH'q hH' hH'H
  have hρK := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSv hKS (m := 1) hρ0
  rw [one_smul] at hρK
  have hτK := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hMv hK (m := 1) hτ0
  rw [one_smul] at hτK
  exact (qLinearlyEquivalent_add_right
      (qLinearlyEquivalent_add_right hρK.symm.qLinearlyEquivalent BS) AS).trans
    (qLinearlyEquivalent_pullback_of_isPullback
      (MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hrange) hgen
      (hD1q.add hAq) hpbD hHq hgH
      ((qLinearlyEquivalent_add_right (qLinearlyEquivalent_add_right hτK.qLinearlyEquivalent B)
        A).trans hlin) H' hH'q hH' hH'H)

/-- **A complement on a dlt pair restricts to every floor component.** Let `(M, B)` be an
effective rational `ℚ`-factorial dlt pair (`MMP.Fourfold.IsPair`, `MMP.Fourfold.IsQFactorial`,
`MMP.Intersection.IsDltPair`) with `g : M ⟶ Z` projective, `K` a canonical divisor of `M`, and
`A ≥ 0` a `ℚ`-Cartier `ℚ`-divisor with `(M, B + A)` log canonical
(`MMP.Intersection.IsLogCanonicalPair`) and `K + B + A ∼_ℚ g^*H`. Let `(S, B_S)` arise from
`(M, B)` by one adjunction step `j : S ⟶ M` (`MMP.Fourfold.IsAdjunctionStep`). Then no component
of `S` maps into `Supp A`, the pull-back `A_S = j^*A` is effective and `ℚ`-Cartier,
`(S, B_S + A_S)` is log canonical, and `K_S + B_S + A_S ∼_ℚ (j ≫ g)^*H'` for every canonical
divisor `K_S` of `S` and every `ℚ`-Cartier `H' ∼_ℚ H` on `Z` whose pull-back to `S` is defined. -/
@[mmp "lem_fourfold_dlt_floor_complement"]
public theorem IsAdjunctionStep.exists_isLogCanonicalPair_add_pullback
    {M Z S : Scheme.{0}} {sM : M ⟶ Spec (.of ℂ)}
    [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {n : ℕ} {K : Divisor M} (hK : K.IsCanonicalDivisor sM (n + 1)) {B A : QDivisor M}
    (hB : IsPair sM B) (hQ : IsQFactorial sM) (hdlt : MMP.Intersection.IsDltPair sM B)
    {g : M ⟶ Z} (hg : IsProjectiveMorphism g)
    (hA0 : 0 ≤ A) (hAq : A.IsQCartier) (hlc : MMP.Intersection.IsLogCanonicalPair sM (B + A))
    {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgH : ∀ T : irreducibleComponents M, g (componentGenericPoint M T) ∉ H.supp)
    (hlin : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent (H.pullback hHq hgH))
    {j : S ⟶ M} {BS : QDivisor S} (hS : IsAdjunctionStep sM B j BS) :
    ∃ hA : ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ A.supp,
      0 ≤ A.pullback hAq hA ∧ (A.pullback hAq hA).IsQCartier ∧
      MMP.Intersection.IsLogCanonicalPair (j ≫ sM) (BS + A.pullback hAq hA) ∧
      ∀ (KS : Divisor S), KS.IsCanonicalDivisor (j ≫ sM) n →
        ∀ (H' : QDivisor Z) (hH'q : H'.IsQCartier)
          (hH' : ∀ T : irreducibleComponents S, (j ≫ g) (componentGenericPoint S T) ∉ H'.supp),
          H'.QLinearlyEquivalent H →
          (Divisor.toQDivisor KS + BS + A.pullback hAq hA).QLinearlyEquivalent
            (H'.pullback hH'q hH') := by
  have hMv : IsNormalVariety ℂ sM := hB.isPair.1
  have : LocallyOfFiniteType sM := hMv.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim M = n + 1 := by rw [hK.1]; push_cast; rfl
  obtain ⟨hSv, P, hP1, hrange, hci, -⟩ := id hS
  have : LocallyOfFiniteType (j ≫ sM) := hSv.1.toLocallyOfFiniteType
  have hdimS : topologicalKrullDim S = n :=
    MMP.Fourfold.topologicalKrullDim_eq_of_range_eq_support sM hdim j P hrange
  have hBP : B.coeff P = 1 := le_antisymm (hdlt.2.1 P) hP1
  have hAP : A.coeff P = 0 := coeff_eq_zero_of_isLogCanonicalPair_add hA0 hlc hBP
  have hA : ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ A.supp :=
    MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hrange hAP
  have hApb : A.IsPullback j hA (A.pullback hAq hA) := QDivisor.isPullback_pullback hAq hA
  have hAS0 : 0 ≤ A.pullback hAq hA := nonneg_of_isPullback j hA0 hAq hApb
  refine ⟨hA, hAS0, hApb.isQCartier hAq, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have := isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero hdimS
    exact ⟨isLogCanonicalPair_of_topologicalKrullDim_eq_zero hSv hdimS _,
      fun KS _ H' hH'q hH' _ => by
        rw [show Divisor.toQDivisor KS + BS + A.pullback hAq hA = H'.pullback hH'q hH' from
          Finsupp.ext isEmptyElim]⟩
  exact hS.isLogCanonicalPair_add_and_qLinearlyEquivalent hnpos hK hdim hB hQ hA0 hAq hlc hHq hgH
    hlin hSv hdimS hrange hBP hAP hApb hAS0

end MMP.Fourfold
