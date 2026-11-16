module

public import MMP.AlgebraicGeometry.Singularities.DltFloor.Residue

/-!
# Uniqueness of adjoint generators on a semi-dlt floor

Let `T` be a reduced `S₂` seminormal scheme with normalization `⨿ᵢ Tᵢ ⟶ T` and `Θᵢ` boundaries on
the `Tᵢ`. Two local generators of the adjoint sheaf of `(T, Θ)` on an open `U` differ by a unit of
`𝒪_T(U)`: their ratio is a unit on each `Tᵢ`, the logarithmic residue presentations along the
double locus show that the values of the ratio agree across the double locus, so the ratio
descends to `T` in codimension one by seminormality, and extends across codimension two since `T`
is `S₂`.

## Main results

* `MMP.Fourfold.SdltFloor.exists_smul_eq_of_isAdjointGeneratorOn`

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.SdltFloor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

/-- The image of a section in the function field does not change under restriction. -/
private theorem germToFunctionField_app_res {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (i : N.ι) {U U' : T.Opens} (hU : U' ≤ U) (f : Γ(T, U))
    [Nonempty (N.n i ⁻¹ᵁ U')] [Nonempty (N.n i ⁻¹ᵁ U)] :
    ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
        ((N.n i).app U' (T.presheaf.map (homOfLE hU).op f)) =
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) := by
  have h := congrArg (fun φ => ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom (φ.hom f))
    ((N.n i).naturality (homOfLE hU).op)
  simp only [CommRingCat.comp_apply] at h
  rw [h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-! ### Functions on the floor and its normalization -/

/-- Every point of `T` lies under a point of some normalization component. -/
private theorem exists_base_eq {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (x : T) : ∃ i z, (N.n i).base z = x := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hsurj : Surjective (slcCurveNormalization T hT) := Scheme.surjective_normalization T hT
  obtain ⟨w, rfl⟩ := hsurj.surj x
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  refine ⟨i, z, ?_⟩
  have h1 : (Limits.Sigma.ι N.X i ≫ φ.hom ≫ slcCurveNormalization T hT).base z =
      (N.n i).base z := by
    rw [hφ, Limits.Sigma.ι_desc]
  have h2 : φ.hom.base (φ.inv.base w) = w := by
    rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
    rfl
  rw [← h1, Scheme.Hom.comp_apply, ← sigmaMk_mk, hz, Scheme.Hom.comp_apply, h2]

/-- **Functions on a reduced scheme are detected on its normalization.** A function on an open
`U` of the reduced scheme `T` whose pull-back to every normalization component meeting `U`
vanishes in the function field is zero. -/
public theorem eq_zero_of_forall_germToFunctionField_eq_zero {k : Type} [Field k]
    {T : Scheme.{0}} [IsReduced T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {U : T.Opens} (b : Γ(T, U))
    (h : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b) = 0) : b = 0 := by
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := exists_base_eq N x
  have hzU : z ∈ N.n i ⁻¹ᵁ U := T.basicOpen_le b hx
  haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hzU⟩⟩
  have hz : z ∈ (N.X i).basicOpen ((N.n i).app U b) := by
    rw [← Scheme.preimage_basicOpen]
    exact hx
  have h0 : (N.n i).app U b = 0 :=
    (N.X i).germToFunctionField_injective (N.n i ⁻¹ᵁ U)
      ((h i inferInstance).trans (map_zero _).symm)
  rw [h0, Scheme.basicOpen_zero] at hz
  exact hz

section SdltUniqueness

open MMP.Flips

variable {k : Type} [Field k] [PerfectField k]

/-! ### Descent of functions along the normalization of a seminormal scheme -/

/-- **Seminormal descent along a finite family of quotients.** Let `A` be a ring in which
`x³ = y²` forces `x = a², y = a³` for some `a` (seminormality), and `p_k : A → B_k` finitely many
surjections onto domains, jointly injective. Suppose that for every `k` some `c_k ∈ A` vanishes in
every `B_l`, `l ≠ k`, with `M_k ⊆ √(p_k(c_k))` for an ideal `M_k` of `B_k`. Then an element
`(f_k)` of `∏ B_k` congruent to the image of a single `r ∈ A` modulo every `M_k` comes from `A`.
The conductor `𝔠 = {b | b ∏ B_k ⊆ A}` contains the `p(c_k)` and is radical by seminormality
(`b² ∈ 𝔠` gives `(bx)², (bx)³ ∈ A`, so `bx ∈ A`), so it contains `f - p(r)`. -/
private theorem exists_eq_of_forall_sub_mem {A : Type*} [CommRing A]
    (hA : ∀ x y : A, x ^ 3 = y ^ 2 → ∃ a : A, x = a ^ 2 ∧ y = a ^ 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ k, CommRing (B k)]
    [∀ k, IsDomain (B k)]
    (p : ∀ k, A →+* B k) (hinj : Function.Injective (Pi.ringHom p))
    (hsurj : ∀ k, Function.Surjective (p k)) (M : ∀ k, Ideal (B k))
    (hc : ∀ k, ∃ c : A, (∀ l, l ≠ k → p l c = 0) ∧ M k ≤ (Ideal.span {p k c}).radical)
    (f : ∀ k, B k) (r : A) (hf : ∀ k, f k - p k r ∈ M k) :
    ∃ a : A, ∀ k, p k a = f k := by
  classical
  set φ := Pi.ringHom p with hφ
  have hφa : ∀ a l, φ a l = p l a := fun _ _ => rfl
  let C : Set (∀ k, B k) := {b | ∀ x, ∃ a, φ a = b * x}
  have hCmul : ∀ b ∈ C, ∀ y, b * y ∈ C := fun b hb y x => by
    obtain ⟨a, ha⟩ := hb (y * x)
    exact ⟨a, by rw [ha, mul_assoc]⟩
  have hCadd : ∀ b ∈ C, ∀ b' ∈ C, b + b' ∈ C := fun b hb b' hb' x => by
    obtain ⟨a, ha⟩ := hb x
    obtain ⟨a', ha'⟩ := hb' x
    exact ⟨a + a', by rw [map_add, ha, ha', add_mul]⟩
  have hCsum : ∀ (s : Finset ι) (b : ι → ∀ k, B k), (∀ k ∈ s, b k ∈ C) → ∑ k ∈ s, b k ∈ C := by
    intro s b hb
    induction s using Finset.induction_on with
    | empty => exact fun x => ⟨0, by simp⟩
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact hCadd _ (hb k (Finset.mem_insert_self _ _)) _
        (ih fun l hl => hb l (Finset.mem_insert_of_mem hl))
  choose c hc0 hcM using hc
  have hφc : ∀ k, φ (c k) ∈ C := fun k x => by
    obtain ⟨a', ha'⟩ := hsurj k (x k)
    refine ⟨c k * a', funext fun l => ?_⟩
    rw [map_mul, Pi.mul_apply, Pi.mul_apply]
    simp only [hφa]
    by_cases hl : l = k
    · subst hl; rw [ha']
    · rw [hc0 k l hl, zero_mul, zero_mul]
  set b : ∀ k, B k := f - φ r with hb
  have hbM : ∀ k, ∃ N : ℕ, ∃ y, b k ^ N = p k (c k) * y := fun k => by
    obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp (hcM k (by
      simpa [hb, hφa] using hf k))
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hN
    exact ⟨N, y, hy.symm.trans (mul_comm _ _)⟩
  choose N y hy using hbM
  set N' := ∑ k, N k with hN'
  have hNk : ∀ k, N k ≤ N' := fun k =>
    Finset.single_le_sum (fun l _ => Nat.zero_le (N l)) (Finset.mem_univ k)
  have hbN : b ^ N' ∈ C := by
    have hdec : b ^ N' = ∑ k, φ (c k) * Pi.single k (b k ^ (N' - N k) * y k) := by
      funext l
      simp only [Pi.pow_apply, Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single l]
      · rw [Pi.single_eq_same, hφa, ← mul_assoc, mul_comm (p l (c l)), mul_assoc, ← hy l,
          ← pow_add, Nat.sub_add_cancel (hNk l)]
      · intro k _ hk
        rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero]
      · exact fun h => absurd (Finset.mem_univ l) h
    rw [hdec]
    exact hCsum _ _ fun k _ => hCmul _ (hφc k) _
  have hsq : ∀ b, b ^ 2 ∈ C → b ∈ C := fun b hb x => by
    obtain ⟨a₂, ha₂⟩ := hb (x ^ 2)
    obtain ⟨a₃, ha₃⟩ := hb (b * x ^ 3)
    have h23 : a₂ ^ 3 = a₃ ^ 2 := hinj (by
      rw [map_pow, map_pow, ha₂, ha₃]; ring)
    obtain ⟨a, h2, h3⟩ := hA a₂ a₃ h23
    refine ⟨a, Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq ?_ ?_⟩
    · rw [← map_pow, ← h2, ha₂]; ring
    · rw [← map_pow, ← h3, ha₃]; ring
  have hpow : ∀ j : ℕ, ∀ b, b ^ (2 ^ j) ∈ C → b ∈ C := by
    intro j
    induction j with
    | zero => intro b hb; simpa using hb
    | succ j ih =>
      intro b hb
      refine ih b (hsq _ ?_)
      rwa [← pow_mul, ← pow_succ]
  have hbC : b ∈ C := by
    refine hpow N' _ ?_
    have hle : N' ≤ 2 ^ N' := (Nat.lt_two_pow_self).le
    rw [← Nat.sub_add_cancel hle, pow_add, mul_comm]
    exact hCmul _ hbN _
  obtain ⟨a', ha'⟩ := hbC 1
  refine ⟨r + a', fun k => ?_⟩
  have := congrFun ha' k
  rw [hφa, mul_one, hb, Pi.sub_apply, hφa] at this
  rw [map_add, this]
  ring

/-- Localizations of seminormal rings satisfy the existence half of seminormality: if
`x³ = y²` in `M⁻¹R`, write `x = X/u²`, `y = Y/u³` and clear the remaining denominator. -/
private theorem exists_sq_cube_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hR : IsSeminormalRing R) {x y : S}
    (h : x ^ 3 = y ^ 2) : ∃ a : S, x = a ^ 2 ∧ y = a ^ 3 := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M x
  obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj M y
  simp only at ha hb
  set X : R := a * s * t ^ 2 with hX
  set Y : R := b * s ^ 3 * t ^ 2 with hY
  have hxu : x * (algebraMap R S s * algebraMap R S t) ^ 2 = algebraMap R S X := by
    simp only [hX, map_mul, map_pow]
    linear_combination (algebraMap R S s * algebraMap R S t ^ 2) * ha
  have hyu : y * (algebraMap R S s * algebraMap R S t) ^ 3 = algebraMap R S Y := by
    simp only [hY, map_mul, map_pow]
    linear_combination (algebraMap R S s ^ 3 * algebraMap R S t ^ 2) * hb
  have hXY : algebraMap R S (X ^ 3) = algebraMap R S (Y ^ 2) := by
    rw [map_pow, map_pow, ← hxu, ← hyu]
    linear_combination (algebraMap R S s * algebraMap R S t) ^ 6 * h
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M S).mp hXY
  have hcube : ((w : R) ^ 2 * X) ^ 3 = ((w : R) ^ 3 * Y) ^ 2 := by
    calc ((w : R) ^ 2 * X) ^ 3 = (w : R) ^ 5 * ((w : R) * X ^ 3) := by ring
      _ = (w : R) ^ 5 * ((w : R) * Y ^ 2) := by rw [hw]
      _ = ((w : R) ^ 3 * Y) ^ 2 := by ring
  obtain ⟨c, ⟨hc2, hc3⟩, -⟩ := hR _ _ hcube
  obtain ⟨v, hv⟩ := IsLocalization.map_units S (w * (s * t))
  have hv' : (v : S) = algebraMap R S w * (algebraMap R S s * algebraMap R S t) := by
    rw [hv]; simp only [Submonoid.coe_mul, map_mul]
  refine ⟨algebraMap R S c * (↑v⁻¹ : S), ?_, ?_⟩
  · have e : algebraMap R S c ^ 2 = x * (↑v : S) ^ 2 := by
      rw [← map_pow, ← hc2, map_mul, ← hxu, hv', map_pow]; ring
    calc x = x * ((↑v : S) * ↑v⁻¹) ^ 2 := by rw [Units.mul_inv, one_pow, mul_one]
      _ = (algebraMap R S c * (↑v⁻¹ : S)) ^ 2 := by rw [mul_pow (algebraMap R S c), e]; ring
  · have e : algebraMap R S c ^ 3 = y * (↑v : S) ^ 3 := by
      rw [← map_pow, ← hc3, map_mul, ← hyu, hv', map_pow]; ring
    calc y = y * ((↑v : S) * ↑v⁻¹) ^ 3 := by rw [Units.mul_inv, one_pow, mul_one]
      _ = (algebraMap R S c * (↑v⁻¹ : S)) ^ 3 := by rw [mul_pow (algebraMap R S c), e]; ring

/-- The local rings of a seminormal scheme satisfy the existence half of seminormality. -/
private theorem stalk_exists_sq_cube {X : Scheme.{0}} (hX : IsSeminormal X) (x : X)
    {a b : X.presheaf.stalk x} (h : a ^ 3 = b ^ 2) : ∃ c, a = c ^ 2 ∧ b = c ^ 3 := by
  obtain ⟨V, hxV, hV⟩ := hX x
  have hVa : IsAffineOpen (V : X.Opens) := V.2
  letI := (X.presheaf.germ (V : X.Opens) x hxV).hom.toAlgebra
  haveI := hVa.isLocalization_stalk ⟨x, hxV⟩
  exact exists_sq_cube_of_isLocalization (hVa.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl hV h

/-- Evaluating equal residues `ḡ₁ (dx̄₁)^{⊗m} = ḡ₂ (dx̄₂)^{⊗m}` of logarithmic pluriforms against
derivations `D₁, …, D_e` of the residue field: `ḡ₁ det(D_a x̄₁_b)^m = ḡ₂ det(D_a x̄₂_b)^m`. -/
private theorem logPluriResidue_eval {k : Type*} [Field k] {O : Type*} [CommRing O]
    {L : Type*} [Field L] [Algebra k L] [Algebra O L] {m e : ℕ} {g₁ g₂ : O} {x₁ x₂ : Fin e → O}
    (h : MMP.Fourfold.logPluriResidue (O := O) k L m e g₁ x₁ =
      MMP.Fourfold.logPluriResidue (O := O) k L m e g₂ x₂) (D : Fin e → Derivation k L L) :
    algebraMap O L g₁ * (Matrix.of fun a b => D a (algebraMap O L (x₁ b))).det ^ m =
      algebraMap O L g₂ * (Matrix.of fun a b => D a (algebraMap O L (x₂ b))).det ^ m := by
  set φ : Fin e → Module.Dual L Ω[L⁄k] := fun a => (D a).liftKaehlerDifferential
  have := congrArg (PiTensorProduct.dualDistrib
    (PiTensorProduct.tprod L fun _ : Fin m =>
      exteriorPower.pairingDual L Ω[L⁄k] e (exteriorPower.ιMulti L e φ))) h
  simp only [MMP.Fourfold.logPluriResidue, map_smul, PiTensorProduct.dualDistrib_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti, smul_eq_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  simp only [φ, Derivation.liftKaehlerDifferential_comp_D] at this
  rw [← Matrix.det_transpose (Matrix.of fun a b => D a (algebraMap O L (x₁ b))),
    ← Matrix.det_transpose (Matrix.of fun a b => D a (algebraMap O L (x₂ b)))]
  convert this using 4 <;> rfl

/-- The logarithmic pluriform `g (t⁻¹ dt ∧ dx)^{⊗m}` of `MMP.Fourfold.logPluriForm`, written with
the case split of `MMP.Fourfold.IsLogResiduePresentation`. -/
private theorem logPluriForm_eq_dite {k K O : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing O] [Algebra O K] (m e : ℕ) (h : O) (t : O) (x : Fin e → O) :
    MMP.Fourfold.logPluriForm (O := O) k K m e h t x =
      algebraMap O K h • PiTensorProduct.tprod K (fun _ : Fin m =>
        exteriorPower.ιMulti K (e + 1) (fun j : Fin (e + 1) => if hj : j.val = 0 then
          (algebraMap O K t)⁻¹ • KaehlerDifferential.D k K (algebraMap O K t) else
          KaehlerDifferential.D k K (algebraMap O K (x ⟨j.val - 1, by omega⟩)))) := by
  unfold MMP.Fourfold.logPluriForm
  congr 2
  funext c
  have hv : (fun j : Fin (e + 1) => if hj : j.val = 0 then
          (algebraMap O K t)⁻¹ • KaehlerDifferential.D k K (algebraMap O K t) else
          KaehlerDifferential.D k K (algebraMap O K (x ⟨j.val - 1, by omega⟩))) =
      Function.update (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t))
        (fun i => KaehlerDifferential.D k K (algebraMap O K (x i))) : Fin (e + 1) → Ω[K⁄k]) 0
        ((algebraMap O K t)⁻¹ • KaehlerDifferential.D k K (algebraMap O K t)) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp
    · rw [dif_neg (by simp), Function.update_of_ne (Fin.succ_ne_zero l), Fin.cons_succ]
      congr 3
  rw [hv, AlternatingMap.map_update_smul, Fin.update_cons_zero]

/-- **Comparing two residue presentations on one branch.** If `s = u s'` on the normalization
component `Tᵢ`, with residue presentations `ε ḡ (dā)^{⊗m}` of `s` and `ε' ḡ' (dā')^{⊗m}` of `s'`
along the prime divisor `P` of `Tᵢ`, then for all derivations `D₁, …, D_e` of `κ(P)`,
`ε ḡ det(D_b ā_c)^m = ū ε' ḡ' det(D_b ā'_c)^m`. -/
private theorem isLogResiduePresentation_eval {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : MMP.Flips.NormalizationComponents sT hT} {m e : ℕ} {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V V' : T.Opens} {hP : (N.n i).base P.genericPoint ∈ V}
    {hP' : (N.n i).base P.genericPoint ∈ V'} {a : Fin (e + 1 - 1) → Γ(T, V)}
    {a' : Fin (e + 1 - 1) → Γ(T, V')} {g : Γ(T, V)} {g' : Γ(T, V')} {ε ε' : ℤ}
    {s s' : RationalPluriForms (N.n i ≫ sT) (e + 1) m}
    (h : IsLogResiduePresentation N (e + 1) m i P V hP a g ε s)
    (h' : IsLogResiduePresentation N (e + 1) m i P V' hP' a' g' ε' s')
    (u : (N.X i).presheaf.stalk P.genericPoint)
    (hu : s = algebraMap _ (N.X i).functionField u • s') :
    letI : Algebra k ((N.X i).residueField P.genericPoint) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n i ≫ sT).appTop ≫
        (N.X i).Γevaluation P.genericPoint).hom.toAlgebra
    ∀ D : Fin e → Derivation k ((N.X i).residueField P.genericPoint)
        ((N.X i).residueField P.genericPoint),
      ((ε : (N.X i).residueField P.genericPoint) * (N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V g))) *
        (Matrix.of fun (b c : Fin e) => D b ((N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP
            ((N.n i).app V (a c))))).det ^ m =
      (N.X i).residue P.genericPoint u *
        ((ε' : (N.X i).residueField P.genericPoint) * (N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' g'))) *
        (Matrix.of fun (b c : Fin e) => D b ((N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP'
            ((N.n i).app V' (a' c))))).det ^ m := by
  letI : Algebra k ((N.X i).residueField P.genericPoint) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n i ≫ sT).appTop ≫
        (N.X i).Γevaluation P.genericPoint).hom.toAlgebra
  intro D
  obtain ⟨z₁, h₁, hz₁, hs₁, -, hr₁⟩ := h
  obtain ⟨z₂, h₂, hz₂, hs₂, -, hr₂⟩ := h'
  beta_reduce at hs₁ hs₂ hr₁ hr₂
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  haveI := P.integral
  have hjP : P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme) = P.genericPoint := rfl
  letI := stalkAlgebra (N.n i ≫ sT) P.genericPoint
  letI := functionFieldAlgebra (N.n i ≫ sT)
  haveI := isScalarTower_stalk_functionField (N.n i ≫ sT) P.genericPoint
  letI : Algebra ((N.X i).presheaf.stalk P.genericPoint) ((N.X i).residueField P.genericPoint) :=
    ((N.X i).residue P.genericPoint).hom.toAlgebra
  haveI : IsScalarTower k ((N.X i).presheaf.stalk P.genericPoint)
      ((N.X i).residueField P.genericPoint) := IsScalarTower.of_algebraMap_eq' rfl
  have hfacts := stalk_facts_of_eq_genericPoint (sY := N.n i ≫ sT) P hjP
  haveI : Module.Free ((N.X i).presheaf.stalk P.genericPoint)
      Ω[(N.X i).presheaf.stalk P.genericPoint⁄k] := hfacts.2.1
  have key := exists_uniformizer_of_eq_genericPoint (sY := N.n i ≫ sT)
    (j := P.idealSheaf.subschemeι) P hjP
  obtain ⟨ϖ, r, hϖ0, hr, hunif⟩ : ∃ (ϖ : (N.X i).presheaf.stalk P.genericPoint)
      (r : Ω[(N.X i).presheaf.stalk P.genericPoint⁄k] →ₗ[(N.X i).presheaf.stalk P.genericPoint]
        (N.X i).presheaf.stalk P.genericPoint),
      (P.idealSheaf.subschemeι.stalkMap (genericPoint P.idealSheaf.subscheme)).hom ϖ = 0 ∧
      r (KaehlerDifferential.D k _ ϖ) = 1 ∧
      ∀ t : (N.X i).presheaf.stalk P.genericPoint,
        (N.X i).ord (algebraMap _ (N.X i).functionField t) P.genericPoint = 1 →
          ∃ v, IsUnit v ∧ t = v * ϖ := by
    obtain ⟨ϖ, r, h1, h2, -, -, h5⟩ := key
    exact ⟨ϖ, r, h1, h2, h5⟩
  have hϖL : algebraMap ((N.X i).presheaf.stalk P.genericPoint)
      ((N.X i).residueField P.genericPoint) ϖ = 0 := by
    have hm : ϖ ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk P.genericPoint) := by
      by_contra hc
      have hu := (IsLocalRing.notMem_maximalIdeal.mp hc).map
        (P.idealSheaf.subschemeι.stalkMap (genericPoint P.idealSheaf.subscheme)).hom
      exact not_isUnit_zero (hϖ0 ▸ hu)
    exact (IsLocalRing.residue_eq_zero_iff ϖ).mpr hm
  have hO : ∀ z : (N.X i).functionField, (N.X i).ord z P.genericPoint = 1 →
      ∃ v : (N.X i).presheaf.stalk P.genericPoint, IsUnit v ∧
        algebraMap _ (N.X i).functionField (v * ϖ) = z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      have := congrFun Scheme.ord_zero P.genericPoint
      simp only [Pi.zero_apply] at this
      omega
    obtain ⟨t, ht⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      P.genericPoint hz0 fun Γ hΓ => by
        obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
        omega
    obtain ⟨v, hv, rfl⟩ := hunif t (by rwa [ht])
    exact ⟨v, hv, ht⟩
  obtain ⟨v₁, hv₁, rfl⟩ := hO z₁ hz₁
  obtain ⟨v₂, hv₂, rfl⟩ := hO z₂ hz₂
  set x₁ : Fin e → (N.X i).presheaf.stalk P.genericPoint := fun l =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V (a l))
  set x₂ : Fin e → (N.X i).presheaf.stalk P.genericPoint := fun l =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' (a' l))
  have e₁ : s = logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) k
      (N.X i).functionField m e h₁ (v₁ * ϖ) x₁ := by
    rw [hs₁, logPluriForm_eq_dite]
  have e₂ : s' = logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) k
      (N.X i).functionField m e h₂ (v₂ * ϖ) x₂ := by
    rw [hs₂, logPluriForm_eq_dite]
  have heq : logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) k
      (N.X i).functionField m e h₁ (v₁ * ϖ) x₁ =
      logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) k
      (N.X i).functionField m e (u * h₂) (v₂ * ϖ) x₂ := by
    have hmul : logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) k
        (N.X i).functionField m e (u * h₂) (v₂ * ϖ) x₂ =
        algebraMap _ (N.X i).functionField u • logPluriForm
          (O := (N.X i).presheaf.stalk P.genericPoint) k (N.X i).functionField m e h₂ (v₂ * ϖ)
          x₂ := by
      simp only [logPluriForm, map_mul, mul_smul]
    exact e₁.symm.trans (hu.trans (by rw [e₂]; exact hmul.symm))
  have hres := logPluriResidue_eq_of_logPluriForm_eq (k := k) (K := (N.X i).functionField)
    (L := (N.X i).residueField P.genericPoint) IsLocalRing.residue_surjective hϖL hr hv₁ hv₂
    x₁ x₂ heq
  have := logPluriResidue_eval hres D
  rw [map_mul] at this
  change (N.X i).residue P.genericPoint h₁ * _ = (N.X i).residue P.genericPoint u *
    (N.X i).residue P.genericPoint h₂ * _ at this
  rwa [hr₁, hr₂] at this

/-- If `(c b)^{⊗n}` is written in the basis `b^{⊗n}` of the `n`-th tensor power of a line,
its coordinate is `cⁿ`. -/
private theorem tprod_smul_eq_smul_basis {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) (c : K) (n : ℕ) :
    ∀ τ : ZTensorPower K L (n : ℤ),
      τ = (PiTensorProduct.tprod K (fun _ : Fin n => c • b ()) : TensorPower K n L) →
      τ = c ^ n • ZTensorPower.basis b n () := by
  rintro τ rfl
  rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  change _ = ((Basis.piTensorProduct fun _ : Fin n => b).reindex (Equiv.ofUnique _ _)) ()
  rw [Module.Basis.reindex_apply, Basis.piTensorProduct_apply]

/-- If `dv₁ ∧ ⋯ ∧ dv_d = c σ` for a generator `σ` of `Ω^d_{A/k}`, then
`(dv₁ ∧ ⋯ ∧ dv_d)^{⊗n}` has coordinate `cⁿ` along `σ^{⊗n}`. -/
private theorem formCoeff_tprod_ιMulti {k A K : Type*} [CommRing k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0)
    {v : Fin d → A} {c : A}
    (hc : exteriorPower.ιMulti A d (fun j => KaehlerDifferential.D k A (v j)) = c • σ)
    (n : ℕ) : ∀ τ : PluriForms k K d n,
      τ = (PiTensorProduct.tprod K (fun _ : Fin n => exteriorPower.ιMulti K d
        (fun j => KaehlerDifferential.D k K (algebraMap A K (v j)))) : TensorPower K n _) →
      formCoeff A hσ h0 τ = algebraMap A K c ^ n := by
  intro τ hτ
  have hv : exteriorPower.ιMulti K d (fun j => KaehlerDifferential.D k K (algebraMap A K (v j))) =
      algebraMap A K c • topFormsBasis A hσ h0 () := by
    have := congrArg (topFormsMap k A K d) hc
    rw [topFormsMap_ιMulti, map_smul] at this
    simp only [KaehlerDifferential.map_D] at this
    rw [topFormsBasis_apply, algebraMap_smul, ← this]
  rw [hv] at hτ
  have := tprod_smul_eq_smul_basis (topFormsBasis A hσ h0) (algebraMap A K c) n τ hτ
  rw [formCoeff, this]
  simp

/-- **Forms built from regular functions are regular.** On a normal variety of dimension `d`,
`(dv₁ ∧ ⋯ ∧ dv_d)^{⊗m}` has no pole along a prime divisor `Γ` when the `vⱼ` are regular at the
generic point of `Γ`. -/
private theorem zero_le_ordForm_tprod_ιMulti {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (Γ : MMP.Mori.PrimeDivisor X) (m : ℕ)
    (v : Fin d → X.presheaf.stalk Γ.genericPoint) :
    letI := functionFieldAlgebra sX
    ∀ τ : RationalPluriForms sX d m,
      τ = (PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti X.functionField d (fun j =>
          KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (v j)))) :
          TensorPower X.functionField m _) →
      τ ≠ 0 → 0 ≤ Γ.ordForm τ := by
  letI := functionFieldAlgebra sX
  intro τ hτ hτ0
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hσ ▸ Submodule.mem_top
    (x := exteriorPower.ιMulti Γ.localRing d fun j => KaehlerDifferential.D k Γ.localRing (v j)))
  have hcoeff := formCoeff_tprod_ιMulti hσ h0 hc.symm m τ hτ
  rw [Γ.ordForm_eq τ hσ h0, hcoeff]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hc0 : algebraMap Γ.localRing X.functionField c ≠ 0 := by
    intro h
    exact hτ0 ((formCoeff_eq_zero_iff (m := (m : ℤ)) hσ h0 τ).1
      (by rw [hcoeff, h, zero_pow hm.ne']))
  rw [← zpow_natCast, MMP.Mori.ord_zpow _ hc0]
  have hv' := (Γ.divisorialValuation_le_one_iff _).2 ⟨c, rfl⟩
  rw [Γ.divisorialValuation_eq_exp_neg_ord hc0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv'
  have hc1 : 0 ≤ X.ord (algebraMap Γ.localRing X.functionField c) Γ.genericPoint := by omega
  exact mul_nonneg (by positivity) hc1

/-- **The residue of a local generator along a conductor component is a unit.** If `s ≠ 0` has
order `-m` along the prime divisor `P` of the normalization component `Tᵢ` and residue presentation
`ε ḡ (dā)^{⊗m}` along `P` with `ε ≠ 0`, then `ḡ(P) ≠ 0`: writing `s = h (t⁻¹ dt ∧ da)^{⊗m}`,
the form `(dt ∧ da)^{⊗m}` has no pole, so `ord_P h ≤ 0` and `h` is a unit. -/
private theorem residue_ne_zero_of_isLogResiduePresentation {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : MMP.Flips.NormalizationComponents sT hT} {m e : ℕ} {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V : T.Opens} {hP : (N.n i).base P.genericPoint ∈ V}
    {a : Fin (e + 1 - 1) → Γ(T, V)} {g : Γ(T, V)} {ε : ℤ} (hε : ε ≠ 0)
    {s : RationalPluriForms (N.n i ≫ sT) (e + 1) m}
    (h : IsLogResiduePresentation N (e + 1) m i P V hP a g ε s)
    (hdim : topologicalKrullDim (N.X i) = ((e + 1 : ℕ) : WithBot ℕ∞)) (hs0 : s ≠ 0)
    (hord : P.ordForm s = -(m : ℤ)) :
    (N.X i).residue P.genericPoint
      ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V g)) ≠ 0 := by
  obtain ⟨z, h₁, hz, hs, -, hr⟩ := h
  beta_reduce at hs hr
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (N.n i ≫ sT)
  have hz0 : z ≠ 0 := by
    rintro rfl
    have := congrFun Scheme.ord_zero P.genericPoint
    simp only [Pi.zero_apply] at this
    omega
  obtain ⟨t, rfl⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    P.genericPoint hz0 fun Γ hΓ => by
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      omega
  set x : Fin e → (N.X i).presheaf.stalk P.genericPoint := fun l =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V (a l))
  set τ : RationalPluriForms (N.n i ≫ sT) (e + 1) m :=
    (PiTensorProduct.tprod (N.X i).functionField (fun _ : Fin m =>
      exteriorPower.ιMulti (N.X i).functionField (e + 1) (fun j =>
        KaehlerDifferential.D k (N.X i).functionField
          (algebraMap _ (N.X i).functionField ((Fin.cons t x : Fin (e + 1) → _) j)))) :
      TensorPower (N.X i).functionField m _) with hτdef
  have hst : s = (algebraMap _ (N.X i).functionField h₁ *
      (algebraMap _ (N.X i).functionField t)⁻¹ ^ m) • τ := by
    have he : s = logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) k
        (N.X i).functionField m e h₁ t x := by
      rw [hs, logPluriForm_eq_dite]
    rw [he, logPluriForm, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_smul, hτdef]
    congr 2
    funext c
    congr 1
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have hτ0 : τ ≠ 0 := by
    rintro h0
    rw [hst, h0, smul_zero] at hs0
    exact hs0 rfl
  have hh0 : algebraMap _ (N.X i).functionField h₁ ≠ 0 := by
    rintro h0
    rw [hst, h0, zero_mul, zero_smul] at hs0
    exact hs0 rfl
  have hc : algebraMap _ (N.X i).functionField h₁ *
      (algebraMap _ (N.X i).functionField t)⁻¹ ^ m ≠ 0 :=
    mul_ne_zero hh0 (pow_ne_zero _ (inv_ne_zero hz0))
  have hτord := zero_le_ordForm_tprod_ιMulti hdim P m (Fin.cons t x) τ rfl hτ0
  rw [hst, P.ordForm_smul_of_topologicalKrullDim_eq hdim hc hτ0, Scheme.ord_mul hh0
    (pow_ne_zero _ (inv_ne_zero hz0)), ← zpow_natCast, MMP.Mori.ord_zpow _ (inv_ne_zero hz0),
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hz0, hz] at hord
  have hh1 : (N.X i).ord (algebraMap _ (N.X i).functionField h₁) P.genericPoint = 0 := by
    have hv' := (P.divisorialValuation_le_one_iff _).2 ⟨h₁, rfl⟩
    rw [P.divisorialValuation_eq_exp_neg_ord hh0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv'
    nlinarith
  obtain ⟨w, hw, hwh⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    P.genericPoint hh0 fun Γ hΓ => by
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      exact hh1
  obtain rfl : w = h₁ := IsFractionRing.injective _ (N.X i).functionField hwh
  intro h0
  have h2 : (N.X i).residue P.genericPoint w ≠ 0 := by
    change IsLocalRing.residue _ w ≠ 0
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.notMem_maximalIdeal.mpr hw)
  rw [hr, h0, mul_zero] at h2
  exact h2 rfl

/-- **Two local generators differ by a unit at every point.** On a normal variety of dimension
`d`, if `s` and `s'` both generate `𝒪(m(K + Θ))` on an open `W`, then at every point `z ∈ W`,
`s = u s'` for a unit `u` of `𝒪_z` (algebraic Hartogs). -/
private theorem exists_isUnit_stalk_smul_eq_of_generatesOn {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) {Θ : QDivisor X} {m : ℕ} {W : X.Opens}
    {s s' : RationalPluriForms sX d m} (hs : GeneratesOn Θ m W s) (hs' : GeneratesOn Θ m W s')
    {z : X} (hz : z ∈ W) :
    ∃ u : X.presheaf.stalk z, IsUnit u ∧ s = algebraMap _ X.functionField u • s' := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set B := ZTensorPower.basis b ((m : ℕ) : ℤ)
  have hc' : B.repr s' () ≠ 0 := repr_ne_zero_of_ne_zero b hs'.1
  set q := B.repr s () / B.repr s' ()
  have hq : s = q • s' := by
    rw [← basis_unit_repr_smul B s, ← basis_unit_repr_smul B s']
    exact (by rw [← mul_smul, div_mul_cancel₀ _ hc'] :
      (B.repr s () • B () : ZTensorPower _ _ _) = q • B.repr s' () • B ())
  have hq0 : q ≠ 0 := div_ne_zero (repr_ne_zero_of_ne_zero b hs.1) hc'
  obtain ⟨u, hu, hqu⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero z hq0
    fun Γ hΓ => by
      have hΓW : (Γ.support ∩ (W : Set X)).Nonempty := ⟨z, hΓ, hz⟩
      have e1 := hs.2 Γ hΓW
      have e2 := hs'.2 Γ hΓW
      rw [hq, Γ.ordForm_smul_of_topologicalKrullDim_eq hd hq0 hs'.1] at e1
      push_cast at e1
      have : ((X.ord q Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
      exact_mod_cast this
  exact ⟨u, hu, by rwa [hqu]⟩

/-- The map `𝒪_{Y,y} ⟶ 𝒪_{X,x}` for `f(x) = y`, on germs. -/
private theorem stalkSpecializes_stalkMap_germ {X Y : Scheme.{0}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f.base x ⤳ y) (V : Y.Opens) (hy : y ∈ V) (e : Γ(Y, V)) :
    (Y.presheaf.stalkSpecializes h ≫ f.stalkMap x).hom (Y.presheaf.germ V y hy e) =
      X.presheaf.germ (f ⁻¹ᵁ V) x (h.mem_open V.isOpen hy) (f.app V e) := by
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- For a closed immersion `f` with `f(x) = y`, `𝒪_{Y,y} ⟶ 𝒪_{X,x}` is surjective. -/
private theorem surjective_stalkSpecializes_stalkMap {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] {x : X} {y : Y} (hxy : f.base x = y) (h : f.base x ⤳ y) :
    Function.Surjective (Y.presheaf.stalkSpecializes h ≫ f.stalkMap x).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact SurjectiveOnStalks.stalkMap_surjective f x

/-- In a local domain of dimension at most one, the maximal ideal lies in the radical of every
nonzero principal ideal. -/
private theorem maximalIdeal_le_radical_span {B : Type*} [CommRing B] [IsLocalRing B] [IsDomain B]
    (hB : ringKrullDim B ≤ 1) {b : B} (hb : b ≠ 0) :
    IsLocalRing.maximalIdeal B ≤ (Ideal.span {b}).radical := by
  haveI : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.2 hB
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J ⟨hJb, hJ⟩ => ?_
  have hJ0 : J ≠ ⊥ := fun h0 => hb (by
    have : b ∈ J := hJb (Ideal.mem_span_singleton_self b)
    rwa [h0, Ideal.mem_bot] at this)
  have hJm := (Ring.krullDimLE_one_iff_of_isPrime_bot.1 inferInstance) J hJ0 hJ
  exact (IsLocalRing.eq_maximalIdeal hJm).ge

/-- Two surjections `p : A → B`, `q : A → C` of local rings induce an isomorphism of residue
fields, both being the residue field of `A`. -/
private theorem exists_residueField_ringEquiv_of_surjective {A B C : Type*} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (p : A →+* B) (q : A →+* C)
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    ∃ τ : IsLocalRing.ResidueField B ≃+* IsLocalRing.ResidueField C,
      ∀ a, τ (IsLocalRing.residue B (p a)) = IsLocalRing.residue C (q a) := by
  set fp := (IsLocalRing.residue B).comp p
  set fq := (IsLocalRing.residue C).comp q
  have hfp : Function.Surjective fp := IsLocalRing.residue_surjective.comp hp
  have hfq : Function.Surjective fq := IsLocalRing.residue_surjective.comp hq
  have hkp : RingHom.ker fp = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective fp hfp)
  have hkq : RingHom.ker fq = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective fq hfq)
  set ep := RingHom.quotientKerEquivOfSurjective hfp
  set eq' := RingHom.quotientKerEquivOfSurjective hfq
  refine ⟨ep.symm.trans ((Ideal.quotEquivOfEq (hkp.trans hkq.symm)).trans eq'), fun a => ?_⟩
  have h1 : ep.symm (IsLocalRing.residue B (p a)) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk]
  rfl

/-- A derivation transported along an isomorphism of algebras. -/
private theorem exists_derivation_transport {R F G : Type*} [CommRing R] [CommRing F]
    [CommRing G] [Algebra R F] [Algebra R G] (τ : F ≃ₐ[R] G) (D : Derivation R F F) :
    ∃ D' : Derivation R G G, ∀ y, D' (τ y) = τ (D y) := by
  refine ⟨Derivation.mk' (τ.toLinearMap ∘ₗ D.toLinearMap ∘ₗ τ.symm.toLinearMap) fun a b => ?_,
    fun y => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
    change τ (D (τ.symm a * τ.symm b)) = a • τ (D (τ.symm b)) + b • τ (D (τ.symm a))
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_add, map_mul,
      map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  · simp

/-- **Residues of the ratio of two local generators agree across a double point.** Let `s, s'` be
local generators of the adjoint of the sdlt scheme `T` on `U` (`MMP.Fourfold.IsAdjointGeneratorOn`)
and `x ∈ U` a point of the double locus lying on two distinct normalization components, over the
codimension-one points `y₀ ∈ T_{k₀}` and `y ∈ T_k`. If `s = u₀ s'` near `y₀` and `s = u s'` near
`y`, and `r ∈ 𝒪_{T,x}` has `r(y₀) = u₀(y₀)`, then `r(y) = u(y)`: evaluating the two residue
presentations of `s` and of `s'` against a derivation `D` with `D(ā') ≠ 0`, transported between
the two branches through `κ(x)`, gives `ū₀ = ū` in `κ(x)`. -/
private theorem residue_eq_of_isAdjointGeneratorOn {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} (hci : ∀ i, IsClosedImmersion (N.n i))
    {n : ℕ} (hdim : ∀ i, topologicalKrullDim (N.X i) = (n : ℕ)) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (Θ i).coeff P = 1)
    {m : ℕ} {U : T.Opens} {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsAdjointGeneratorOn N n m Θ U s) (hs' : IsAdjointGeneratorOn N n m Θ U s')
    {x : T} (hxU : x ∈ U) (hxD : x ∈ (doubleIntersectionLocus T : Set T))
    {k₀ k₁ : N.ι} (hk : k₀ ≠ k₁) {y₀ : N.X k₀} {y : N.X k₁}
    (hy₀ : (N.n k₀).base y₀ = x) (hy : (N.n k₁).base y = x)
    (hc₀ : Order.coheight y₀ = 1) (hc : Order.coheight y = 1)
    (h₀ : (N.n k₀).base y₀ ⤳ x) (h : (N.n k₁).base y ⤳ x)
    {u₀ : (N.X k₀).presheaf.stalk y₀} {u : (N.X k₁).presheaf.stalk y}
    (hu₀ : s k₀ = algebraMap _ (N.X k₀).functionField u₀ • s' k₀)
    (hu : s k₁ = algebraMap _ (N.X k₁).functionField u • s' k₁)
    (r : T.presheaf.stalk x)
    (hr : IsLocalRing.residue _ ((T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap y₀).hom r) =
      IsLocalRing.residue _ u₀) :
    IsLocalRing.residue _ ((T.presheaf.stalkSpecializes h ≫ (N.n k₁).stalkMap y).hom r) =
      IsLocalRing.residue _ u := by
  classical
  obtain ⟨P₀, rfl⟩ : ∃ P : MMP.Mori.PrimeDivisor (N.X k₀), P.genericPoint = y₀ :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y₀ hc₀,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc₀⟩
  obtain ⟨P, rfl⟩ : ∃ P : MMP.Mori.PrimeDivisor (N.X k₁), P.genericPoint = y :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc⟩
  subst hy₀
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  obtain ⟨e, rfl⟩ := exists_eq_add_one_of_primeDivisor (N.n k₀ ≫ sT) (hdim k₀) P₀
  have h₄ : (⟨k₀, P₀.genericPoint⟩ : Σ i, N.X i) ≠ ⟨k₁, P.genericPoint⟩ :=
    fun he => hk (congrArg Sigma.fst he)
  obtain ⟨V, hP₀V, hPV, a, g, hpr₀, hpr⟩ := hs.2 k₀ k₁ P₀ P hy.symm hxU hxD h₄
  obtain ⟨V', hP₀V', hPV', a', g', hpr₀', hpr'⟩ := hs'.2 k₀ k₁ P₀ P hy.symm hxU hxD h₄
  -- the two residue fields, with the `k`-structures of the presentations
  letI alg₀ : Algebra k ((N.X k₀).residueField P₀.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n k₀ ≫ sT).appTop ≫
      (N.X k₀).Γevaluation P₀.genericPoint).hom.toAlgebra
  letI alg : Algebra k ((N.X k₁).residueField P.genericPoint) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (N.n k₁ ≫ sT).appTop ≫
      (N.X k₁).Γevaluation P.genericPoint).hom.toAlgebra
  -- the identification of the residue fields through `κ(x)`
  haveI := hci k₀
  haveI := hci k₁
  obtain ⟨τ, hτ⟩ : ∃ τ : (N.X k₀).residueField P₀.genericPoint ≃+*
      (N.X k₁).residueField P.genericPoint, ∀ a,
      τ ((N.X k₀).residue P₀.genericPoint
        ((T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap P₀.genericPoint).hom a)) =
      (N.X k₁).residue P.genericPoint
        ((T.presheaf.stalkSpecializes h ≫ (N.n k₁).stalkMap P.genericPoint).hom a) :=
    exists_residueField_ringEquiv_of_surjective
      (T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap P₀.genericPoint).hom
      (T.presheaf.stalkSpecializes h ≫ (N.n k₁).stalkMap P.genericPoint).hom
      (surjective_stalkSpecializes_stalkMap _ rfl h₀) (surjective_stalkSpecializes_stalkMap _ hy h)
  have hgerm : ∀ (W : T.Opens) (hW : (N.n k₀).base P₀.genericPoint ∈ W) (f : Γ(T, W)),
      τ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ W)
          P₀.genericPoint hW ((N.n k₀).app W f))) =
        (N.X k₁).residue P.genericPoint ((N.X k₁).presheaf.germ ((N.n k₁) ⁻¹ᵁ W)
          P.genericPoint (h.mem_open W.isOpen hW) ((N.n k₁).app W f)) := by
    intro W hW f
    have e₀ := stalkSpecializes_stalkMap_germ (N.n k₀) h₀ W hW f
    have e₁ := stalkSpecializes_stalkMap_germ (N.n k₁) h W hW f
    have := hτ (T.presheaf.germ W _ hW f)
    rwa [e₀, e₁] at this
  -- `τ` is `k`-linear
  have hcomp₀ : ∀ c : k, algebraMap k ((N.X k₀).residueField P₀.genericPoint) c =
      (N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ ⊤)
        P₀.genericPoint trivial
        ((N.n k₀).app ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop).hom c))) := fun c => rfl
  have hcomp : ∀ c : k, algebraMap k ((N.X k₁).residueField P.genericPoint) c =
      (N.X k₁).residue P.genericPoint ((N.X k₁).presheaf.germ ((N.n k₁) ⁻¹ᵁ ⊤)
        P.genericPoint (h.mem_open (⊤ : T.Opens).isOpen trivial)
        ((N.n k₁).app ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop).hom c))) := fun c => rfl
  let τA : (N.X k₀).residueField P₀.genericPoint ≃ₐ[k] (N.X k₁).residueField P.genericPoint :=
    AlgEquiv.ofRingEquiv (f := τ) fun c => by
      rw [hcomp₀, hgerm ⊤ trivial, hcomp]
  -- derivations `D₀` of `κ(P₀)` with `det(D₀_b ā'_c) = 1`
  obtain ⟨-, -, -, -, hda', -⟩ := id hpr₀'
  set v : Fin e → Ω[(N.X k₀).residueField P₀.genericPoint⁄k] := fun c =>
    KaehlerDifferential.D k ((N.X k₀).residueField P₀.genericPoint)
      ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
        P₀.genericPoint hP₀V' ((N.n k₀).app V' (a' c)))) with hvdef
  have hv : LinearIndependent ((N.X k₀).residueField P₀.genericPoint) v := by
    by_contra hli
    exact hda' ((exteriorPower.ιMulti _ _).map_linearDependent v hli)
  have hφ : ∀ b : Fin e, ∃ φ : Module.Dual ((N.X k₀).residueField P₀.genericPoint)
      Ω[(N.X k₀).residueField P₀.genericPoint⁄k], ∀ c, φ (v c) = if c = b then 1 else 0 := by
    intro b
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord b)
    refine ⟨φ, fun c => ?_⟩
    have h1 := LinearMap.congr_fun hφ ((Module.Basis.span hv) c)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
      Submodule.subtype_apply, Module.Basis.span_apply] at h1
    rw [h1, Finsupp.single_apply]
  choose φ hφ using hφ
  set D₀ : Fin e → Derivation k ((N.X k₀).residueField P₀.genericPoint)
      ((N.X k₀).residueField P₀.genericPoint) := fun b =>
    (φ b).compDer (KaehlerDifferential.D k ((N.X k₀).residueField P₀.genericPoint))
  have hdet : (Matrix.of fun (b c : Fin e) => D₀ b ((N.X k₀).residue P₀.genericPoint
      ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V') P₀.genericPoint hP₀V'
        ((N.n k₀).app V' (a' c))))).det = 1 := by
    have hM : (Matrix.of fun (b c : Fin e) => D₀ b ((N.X k₀).residue P₀.genericPoint
        ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V') P₀.genericPoint hP₀V'
          ((N.n k₀).app V' (a' c))))) = 1 := by
      ext b c
      change φ b (v c) = _
      rw [hφ, Matrix.one_apply]
      by_cases hbc : b = c
      · subst hbc; simp
      · rw [if_neg (Ne.symm hbc), if_neg hbc]
    rw [hM, Matrix.det_one]
  choose D hD using fun b => exists_derivation_transport τA (D₀ b)
  -- the two evaluations
  have E₀ := isLogResiduePresentation_eval hpr₀ hpr₀' u₀ hu₀ D₀
  have E := isLogResiduePresentation_eval hpr hpr' u hu D
  have hMτ : ∀ (W : T.Opens) (hW : (N.n k₀).base P₀.genericPoint ∈ W) (f : Fin e → Γ(T, W)),
      (Matrix.of fun (b c : Fin e) => D b ((N.X k₁).residue P.genericPoint ((N.X k₁).presheaf.germ
          ((N.n k₁) ⁻¹ᵁ W) P.genericPoint (h.mem_open W.isOpen hW) ((N.n k₁).app W (f c))))).det =
        τ (Matrix.of fun (b c : Fin e) => D₀ b ((N.X k₀).residue P₀.genericPoint
          ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ W) P₀.genericPoint hW
            ((N.n k₀).app W (f c))))).det := by
    intro W hW f
    rw [show τ (Matrix.of fun (b c : Fin e) => D₀ b ((N.X k₀).residue P₀.genericPoint
        ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ W) P₀.genericPoint hW
          ((N.n k₀).app W (f c))))).det = (τ : _ →+* _) (Matrix.of fun (b c : Fin e) => D₀ b
          ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ W)
            P₀.genericPoint hW ((N.n k₀).app W (f c))))).det from rfl, RingHom.map_det]
    congr 1
    ext b c
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
      ← hgerm W hW (f c)]
    exact hD b _
  rw [hMτ V hP₀V a, hMτ V' hP₀V' a', ← hgerm V hP₀V g, ← hgerm V' hP₀V' g'] at E
  have E₀' := congrArg τ E₀
  simp only [map_mul, map_pow, map_intCast] at E₀'
  obtain ⟨Δ', hΔ'⟩ : ∃ Δ',
    (Matrix.of fun (b c : Fin e) => D₀ b ((N.X k₀).residue P₀.genericPoint
      ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V') P₀.genericPoint hP₀V'
        ((N.n k₀).app V' (a' c))))).det = Δ' := ⟨_, rfl⟩
  rw [hΔ'] at hdet E₀' E
  -- nonvanishing
  have hord : P₀.ordForm (s' k₀) = -(m : ℤ) := by
    have := (hs'.1 k₀).2 P₀ ⟨P₀.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P₀,
      hxU⟩
    rw [hΘ k₀ P₀ hxD, mul_one] at this
    have h2 : ((P₀.ordForm (s' k₀) : ℤ) : ℚ) = ((-(m : ℤ) : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2
  have hg0 := residue_ne_zero_of_isLogResiduePresentation one_ne_zero hpr₀' (hdim k₀)
    (hs'.1 k₀).1 hord
  have hY : τ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
        P₀.genericPoint hP₀V' ((N.n k₀).app V' g'))) * τ Δ' ^ m ≠ 0 :=
    mul_ne_zero ((map_ne_zero τ).mpr hg0)
      (pow_ne_zero _ ((map_ne_zero τ).mpr fun h0 => one_ne_zero (hdet.symm.trans h0)))
  have hsign : (((-1 : ℤ) ^ m : ℤ) : (N.X k₁).residueField P.genericPoint) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have key : τ ((N.X k₀).residue P₀.genericPoint u₀) = (N.X k₁).residue P.genericPoint u := by
    have h3 : (((-1 : ℤ) ^ m : ℤ) : (N.X k₁).residueField P.genericPoint) *
        (τ ((N.X k₀).residue P₀.genericPoint u₀) - (N.X k₁).residue P.genericPoint u) *
        (τ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
          P₀.genericPoint hP₀V' ((N.n k₀).app V' g'))) * τ Δ' ^ m) = 0 := by
      push_cast at E E₀' ⊢
      linear_combination E - (-1 : (N.X k₁).residueField P.genericPoint) ^ m * E₀'
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hsign
      · exact sub_eq_zero.mp h5
    · exact absurd h4 hY
  have h6 := hτ r
  rw [show (N.X k₀).residue P₀.genericPoint
      ((T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap P₀.genericPoint).hom r) =
      (N.X k₀).residue P₀.genericPoint u₀ from hr, key] at h6
  exact h6.symm

/-- The union of the components not passing through `x` is closed. -/
private theorem isClosed_iUnion_range_of_notMem {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [Finite N.ι] (hci : ∀ i, IsClosedImmersion (N.n i))
    (x : T) : IsClosed (⋃ (i : N.ι) (_ : x ∉ Set.range (N.n i).base), Set.range (N.n i).base) :=
  isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => by
    haveI := hci i
    exact (N.n i).isClosedEmbedding.isClosed_range

/-- **Functions on `T` are detected on the components through a point.** A germ at `x` of the
reduced scheme `T` vanishing on every normalization component through `x` is zero. -/
private theorem stalk_eq_zero_of_forall_stalkMap {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i)) {x : T}
    (y : ∀ i : {i // x ∈ Set.range (N.n i).base}, N.X i.1)
    (hy : ∀ i : {i // x ∈ Set.range (N.n i).base}, (N.n i.1).base (y i) ⤳ x)
    (a : T.presheaf.stalk x)
    (ha : ∀ i : {i // x ∈ Set.range (N.n i).base},
      (T.presheaf.stalkSpecializes (hy i) ≫ (N.n i.1).stalkMap (y i)).hom a = 0) :
    a = 0 := by
  classical
  obtain ⟨V₀, hxV₀, e, rfl⟩ := TopCat.Presheaf.germ_exist T.presheaf a
  set C := ⋃ (i : N.ι) (_ : x ∉ Set.range (N.n i).base), Set.range (N.n i).base
  have hC := isClosed_iUnion_range_of_notMem N hci x
  have hxC : x ∉ C := by
    intro h
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
    exact hi hxi
  set V : T.Opens := V₀ ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hxV : x ∈ V := ⟨hxV₀, hxC⟩
  have hVV₀ : V ≤ V₀ := inf_le_left
  have hres : T.presheaf.map (homOfLE hVV₀).op e = 0 := by
    refine eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_
    have hz := hi.some.2
    set z := hi.some.1
    have hxi : x ∈ Set.range (N.n i).base := by
      by_contra hxi
      exact hz.2 (Set.mem_iUnion₂.mpr ⟨i, hxi, z, rfl⟩)
    set k : {i // x ∈ Set.range (N.n i).base} := ⟨i, hxi⟩
    have hyV : y k ∈ N.n k.1 ⁻¹ᵁ V := (hy k).mem_open V.isOpen hxV
    have h1 := ha k
    rw [← TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hVV₀) x hxV e,
      stalkSpecializes_stalkMap_germ] at h1
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hyV]
    exact (congrArg (algebraMap _ _) h1).trans (map_zero _)
  rw [← TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hVV₀) x hxV e, hres, map_zero]

/-- **A germ vanishing on all components through `x` but one.** For components `l ≠ k` through
`x`, there is a germ at `x` vanishing on the `T_l` but not on `T_k`: a function on an affine
neighbourhood of `x` with a basic open containing the generic point of `T_k` and avoiding the
other components. -/
private theorem exists_stalk_vanishing {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i))
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base) {x : T}
    (y : ∀ i : {i // x ∈ Set.range (N.n i).base}, N.X i.1)
    (hy : ∀ i : {i // x ∈ Set.range (N.n i).base}, (N.n i.1).base (y i) ⤳ x)
    (k : {i // x ∈ Set.range (N.n i).base}) :
    ∃ c : T.presheaf.stalk x,
      (∀ l : {i // x ∈ Set.range (N.n i).base}, l ≠ k →
        (T.presheaf.stalkSpecializes (hy l) ≫ (N.n l.1).stalkMap (y l)).hom c = 0) ∧
      (T.presheaf.stalkSpecializes (hy k) ≫ (N.n k.1).stalkMap (y k)).hom c ≠ 0 := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVa : IsAffineOpen V := hV
  set Z := ⋃ (j : N.ι) (_ : j ≠ k.1), Set.range (N.n j).base
  have hZ : IsClosed Z := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => by
    haveI := hci j
    exact (N.n j).isClosedEmbedding.isClosed_range
  have hηx : (N.n k.1).base (genericPoint (N.X k.1)) ⤳ x :=
    (((genericPoint_spec (N.X k.1)).specializes trivial).map (N.n k.1).base.hom.continuous).trans
      (hy k)
  have hηV : (N.n k.1).base (genericPoint (N.X k.1)) ∈ V := hηx.mem_open V.isOpen hxV
  set W : T.Opens := V ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨f, hfW, hηf⟩ := hVa.exists_basicOpen_le (V := W) ⟨_, hηV, hgen k⟩ hηV
  refine ⟨T.presheaf.germ V x hxV f, fun l hl => ?_, ?_⟩
  · rw [stalkSpecializes_stalkMap_germ]
    have h0 : (N.n l.1).app V f = 0 := by
      rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
      refine eq_bot_iff.mpr fun z hz => ?_
      have := (hfW hz).2
      exact this (Set.mem_iUnion₂.mpr ⟨l, fun h => hl (Subtype.ext h), z, rfl⟩)
    rw [h0, map_zero]
  · rw [stalkSpecializes_stalkMap_germ]
    intro h0
    have hne : (N.n k.1).app V f ≠ 0 := by
      intro h1
      have : genericPoint (N.X k.1) ∈ (N.X k.1).basicOpen ((N.n k.1).app V f) := by
        rw [← Scheme.preimage_basicOpen]
        exact hηf
      rwa [h1, Scheme.basicOpen_zero] at this
    exact hne (germ_injective_of_isIntegral _ _ _ (h0.trans (map_zero _).symm))

/-- A point with a proper generalization and a local ring of dimension at most one has
coheight one. -/
private theorem coheight_eq_one_of_lt {X : Scheme.{0}} {y η : X} (hηy : η ⤳ y) (hne : η ≠ y)
    (hd : ringKrullDim (X.presheaf.stalk y) ≤ 1) : Order.coheight y = 1 := by
  have h1 : Order.coheight y ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hd
    exact_mod_cast hd
  have h0 : Order.coheight y ≠ 0 := by
    rw [Ne, Order.coheight_eq_zero]
    intro hmax
    have hle : y ≤ η := hηy
    exact hne (hηy.antisymm (hmax hle)).eq
  exact le_antisymm h1 (ENat.one_le_iff_ne_zero.mpr h0)

/-- **Local descent of the ratio of two adjoint generators.** Let `T` be a reduced seminormal
scheme whose normalization components `νᵢ : Tᵢ ⟶ T` are closed immersions with distinct
generic points, and `s, s'` local generators of the adjoint of `T` on `U`. Near every point
`x ∈ U` which lies on a single component, or whose local ring has dimension at most one, there
is a function `e` with `sᵢ = ν^*e · s'ᵢ`: the ratios `uₖ = sₖ / s'ₖ` are units at the points over
`x`, agree in `κ(x)` (`residue_eq_of_isAdjointGeneratorOn`), and so come from `𝒪_{T,x}` by
seminormality (`exists_eq_of_forall_sub_mem`). -/
private theorem exists_local_smul_eq_of_isAdjointGeneratorOn {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] (hsn : IsSeminormal T) [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i))
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base)
    {n : ℕ} (hdim : ∀ i, topologicalKrullDim (N.X i) = (n : ℕ)) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (Θ i).coeff P = 1)
    {m : ℕ} {U : T.Opens} {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsAdjointGeneratorOn N n m Θ U s) (hs' : IsAdjointGeneratorOn N n m Θ U s')
    (x : T) (hxU : x ∈ U)
    (hx : ringKrullDim (T.presheaf.stalk x) ≤ 1 ∨
      ∀ i j, x ∈ Set.range (N.n i).base → x ∈ Set.range (N.n j).base → i = j) :
    ∃ V : T.Opens, x ∈ V ∧ V ≤ U ∧ ∃ e : Γ(T, V), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ V)),
      s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V e) • s' i := by
  classical
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  haveI : Fintype {i // x ∈ Set.range (N.n i).base} := Fintype.ofFinite _
  choose y hyx using fun k : {i // x ∈ Set.range (N.n i).base} => k.2
  have hy : ∀ k : {i // x ∈ Set.range (N.n i).base}, (N.n k.1).base (y k) ⤳ x :=
    fun k => by rw [hyx k]
  set p : ∀ k : {i // x ∈ Set.range (N.n i).base},
      T.presheaf.stalk x →+* (N.X k.1).presheaf.stalk (y k) := fun k =>
    (T.presheaf.stalkSpecializes (hy k) ≫ (N.n k.1).stalkMap (y k)).hom with hpdef
  have hsurj : ∀ k, Function.Surjective (p k) := fun k => by
    haveI := hci k.1
    exact surjective_stalkSpecializes_stalkMap _ (hyx k) (hy k)
  have hinj : Function.Injective (Pi.ringHom p) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact stalk_eq_zero_of_forall_stalkMap N hci y hy a fun k => congrFun ha k
  have hyU : ∀ k : {i // x ∈ Set.range (N.n i).base}, y k ∈ N.n k.1 ⁻¹ᵁ U := fun k => by
    change (N.n k.1).base (y k) ∈ U
    rw [hyx k]
    exact hxU
  choose u hu hsu using fun k : {i // x ∈ Set.range (N.n i).base} =>
    exists_isUnit_stalk_smul_eq_of_generatesOn (hdim k.1) (hs.1 k.1) (hs'.1 k.1) (hyU k)
  obtain ⟨i₀, z₀, hz₀⟩ := exists_base_eq N x
  set k₀ : {i // x ∈ Set.range (N.n i).base} := ⟨i₀, z₀, hz₀⟩
  obtain ⟨r, hr⟩ := hsurj k₀ (u k₀)
  -- the descended germ
  obtain ⟨a, ha⟩ : ∃ a, ∀ k, p k a = u k := by
    by_cases hsingle : ∀ k k' : {i // x ∈ Set.range (N.n i).base}, k = k'
    · exact ⟨r, fun k => by rwa [hsingle k k₀]⟩
    push Not at hsingle
    obtain ⟨k₁, k₂, h12⟩ := hsingle
    have hxd : ringKrullDim (T.presheaf.stalk x) ≤ 1 := hx.resolve_right fun h =>
      h12 (Subtype.ext (h k₁.1 k₂.1 k₁.2 k₂.2))
    have hdimB : ∀ k, ringKrullDim ((N.X k.1).presheaf.stalk (y k)) ≤ 1 := fun k =>
      (ringKrullDim_le_of_surjective (p k) (hsurj k)).trans hxd
    choose c hc0 hck using fun k => exists_stalk_vanishing N hci hgen y hy k
    -- every component through `x` has another one
    have hother : ∀ k : {i // x ∈ Set.range (N.n i).base}, ∃ k', k' ≠ k := fun k => by
      by_cases h1 : k₁ = k
      · exact ⟨k₂, fun h => h12 (h1.trans h.symm)⟩
      · exact ⟨k₁, h1⟩
    -- the points over `x` have coheight one
    have hcoh : ∀ k, Order.coheight (y k) = 1 := fun k => by
      obtain ⟨k', hk'⟩ := hother k
      refine coheight_eq_one_of_lt ((genericPoint_spec (N.X k.1)).specializes trivial)
        (fun h => hgen k.1 (Set.mem_iUnion₂.mpr ⟨k'.1, fun h' => hk' (Subtype.ext h'),
          ⟨y k', by rw [hyx k', h, hyx k]⟩⟩)) (hdimB k)
    -- `x` lies on the double locus
    have hxD : x ∈ (doubleIntersectionLocus T : Set T) := by
      refine subset_closure ⟨?_, fun hreg => ?_⟩
      · obtain ⟨k', hk'⟩ := hother k₀
        refine coheight_eq_one_of_lt (((genericPoint_spec (N.X k₀.1)).specializes trivial).map
          (N.n k₀.1).base.hom.continuous |>.trans (hy k₀)) (fun h => hgen k₀.1
            (Set.mem_iUnion₂.mpr ⟨k'.1, fun h' => hk' (Subtype.ext h'), by rw [h]; exact k'.2⟩))
          hxd
      · haveI := IsRegularLocalRing.isDomain (T.presheaf.stalk x)
        have h0 : c k₁ * c k₂ = 0 := hinj (by
          funext l
          show p l (c k₁ * c k₂) = p l 0
          rw [map_zero, map_mul]
          by_cases hl : l = k₁
          · subst hl
            rw [hc0 k₂ l h12, mul_zero]
          · rw [hc0 k₁ l hl, zero_mul])
        rcases mul_eq_zero.mp h0 with h | h
        · exact hck k₁ (by rw [h, map_zero])
        · exact hck k₂ (by rw [h, map_zero])
    refine exists_eq_of_forall_sub_mem (fun _ _ h => stalk_exists_sq_cube hsn x h) p hinj hsurj
      (fun k => IsLocalRing.maximalIdeal _)
      (fun k => ⟨c k, hc0 k, maximalIdeal_le_radical_span (hdimB k) (hck k)⟩) u r fun k => ?_
    by_cases hk : k = k₀
    · subst hk
      rw [hr, sub_self]
      exact zero_mem _
    have hres := residue_eq_of_isAdjointGeneratorOn hci hdim hΘ hs hs' hxU hxD
      (fun h => hk (Subtype.ext h).symm) (hyx k₀) (hyx k) (hcoh k₀) (hcoh k) (hy k₀) (hy k)
      (hsu k₀) (hsu k) r (by rw [show (T.presheaf.stalkSpecializes (hy k₀) ≫
        (N.n k₀.1).stalkMap (y k₀)).hom r = u k₀ from hr])
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub]
    exact sub_eq_zero.mpr hres.symm
  -- the function near `x`
  obtain ⟨V₀, hxV₀, e, he⟩ := TopCat.Presheaf.germ_exist T.presheaf a
  set C := ⋃ (i : N.ι) (_ : x ∉ Set.range (N.n i).base), Set.range (N.n i).base
  have hC := isClosed_iUnion_range_of_notMem N hci x
  have hxC : x ∉ C := by
    intro h
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
    exact hi hxi
  set V : T.Opens := V₀ ⊓ U ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hxV : x ∈ V := ⟨⟨hxV₀, hxU⟩, hxC⟩
  have hVV₀ : V ≤ V₀ := fun z hz => hz.1.1
  refine ⟨V, hxV, fun z hz => hz.1.2, T.presheaf.map (homOfLE hVV₀).op e, fun i hi => ?_⟩
  have hz := hi.some.2
  have hxi : x ∈ Set.range (N.n i).base := by
    by_contra hxi
    exact hz.2 (Set.mem_iUnion₂.mpr ⟨i, hxi, hi.some.1, rfl⟩)
  set k : {i // x ∈ Set.range (N.n i).base} := ⟨i, hxi⟩
  have hyV : y k ∈ N.n k.1 ⁻¹ᵁ V := (hy k).mem_open V.isOpen hxV
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hyV]
  have hgerm : (N.X k.1).presheaf.germ (N.n k.1 ⁻¹ᵁ V) (y k) hyV
      ((N.n k.1).app V (T.presheaf.map (homOfLE hVV₀).op e)) = u k := by
    rw [← stalkSpecializes_stalkMap_germ (N.n k.1) (hy k) V hxV,
      TopCat.Presheaf.germ_res_apply, he]
    exact ha k
  rw [hgerm]
  exact hsu k

/-- In `WithBot ℕ∞`, a dimension that is not at most one is at least two. -/
private theorem two_le_of_not_le_one {d : WithBot ℕ∞} (h : ¬ d ≤ 1) : 2 ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.mpr le_top
    | coe n =>
      have : ¬ n ≤ 1 := fun hn => h (by exact_mod_cast hn)
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast (show 2 ≤ n by omega))

/-- **Gluing coefficients along the normalization, and extending them across codimension two.**
Let `T` be reduced and `S₂` with normalization components `νᵢ : Tᵢ ⟶ T`, and let `s, s'` be
families of forms on the `Tᵢ` with `s'ᵢ ≠ 0`. Suppose every point `x ∈ U` that has a local ring of
dimension at most one, or that lies on a single component, has a neighbourhood `V` and a function
`e` on `V` with `sᵢ = ν^*e · s'ᵢ`. Then there is such a function on all of `U`: the local
functions agree on overlaps, as they are detected on the normalization, and the glued function
on the union `W'` extends across `U ∖ W'`, whose local rings have dimension at least two. -/
private theorem exists_smul_eq_of_forall_exists_local {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [IsLocallyNoetherian T]
    (hS2 : SatisfiesS2 T) {n m : ℕ} {U : T.Opens}
    {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m} (hs'0 : ∀ i, s' i ≠ 0)
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base)
    (hloc : ∀ x ∈ U, (ringKrullDim (T.presheaf.stalk x) ≤ 1 ∨
        ∀ i j, x ∈ Set.range (N.n i).base → x ∈ Set.range (N.n j).base → i = j) →
      ∃ V : T.Opens, x ∈ V ∧ V ≤ U ∧ ∃ e : Γ(T, V), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ V)),
        s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V e) • s' i) :
    ∃ e : Γ(T, U), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e) • s' i := by
  classical
  set J := {x : T // x ∈ U ∧ (ringKrullDim (T.presheaf.stalk x) ≤ 1 ∨
    ∀ i j, x ∈ Set.range (N.n i).base → x ∈ Set.range (N.n j).base → i = j)}
  choose V hxV hVU e he using fun x : J => hloc x.1 x.2.1 x.2.2
  set W' : T.Opens := ⨆ x : J, V x with hW'
  have hVW : ∀ x : J, V x ≤ W' := fun x => le_iSup V x
  have hW'U : W' ≤ U := iSup_le hVU
  -- the local functions agree on overlaps
  have hcompat : TopCat.Presheaf.IsCompatible T.presheaf V e := by
    intro x y
    refine sub_eq_zero.mp (eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_)
    haveI := hi
    haveI : Nonempty (N.n i ⁻¹ᵁ V x) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    haveI : Nonempty (N.n i ⁻¹ᵁ V y) := ⟨⟨hi.some.1, hi.some.2.2⟩⟩
    have h1 := he x i inferInstance
    have h2 := he y i inferInstance
    rw [map_sub, map_sub]
    erw [germToFunctionField_app_res N i inf_le_left, germToFunctionField_app_res N i inf_le_right]
    refine sub_eq_zero.mpr (smul_left_injective _ (hs'0 i) ?_)
    exact h1.symm.trans h2
  obtain ⟨e', he', -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := T.sheaf) V W'
    (fun x => homOfLE (hVW x)) (fun z hz => by
      obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx⟩) e hcompat
  -- extension across codimension two
  have hcodim : ∀ z ∈ U, z ∉ W' → 2 ≤ ringKrullDim (T.presheaf.stalk z) := by
    intro z hz hzW
    refine two_le_of_not_le_one fun hd => hzW ?_
    exact hVW ⟨z, hz, Or.inl hd⟩ (hxV _)
  obtain ⟨E, hE⟩ := (MMP.Flips.bijective_presheaf_map_of_satisfiesS2 hS2 hW'U hcodim).2 e'
  refine ⟨E, fun i hi => ?_⟩
  -- the generic point of `Tᵢ` lies on a single component
  obtain ⟨⟨z, hz⟩⟩ := hi
  have hηU : (N.n i).base (genericPoint (N.X i)) ∈ U :=
    ((genericPoint_spec (N.X i)).specializes trivial).map
      (N.n i).base.hom.continuous |>.mem_open U.isOpen hz
  have hone : ∀ a b, (N.n i).base (genericPoint (N.X i)) ∈ Set.range (N.n a).base →
      (N.n i).base (genericPoint (N.X i)) ∈ Set.range (N.n b).base → a = b := by
    intro a b ha hb
    have hai : a = i := by
      by_contra h
      exact hgen i (Set.mem_iUnion₂.mpr ⟨a, h, ha⟩)
    have hbi : b = i := by
      by_contra h
      exact hgen i (Set.mem_iUnion₂.mpr ⟨b, h, hb⟩)
    rw [hai, hbi]
  set x₀ : J := ⟨_, hηU, Or.inr hone⟩
  haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hz⟩⟩
  haveI : Nonempty (N.n i ⁻¹ᵁ V x₀) := ⟨⟨genericPoint (N.X i), hxV x₀⟩⟩
  rw [← germToFunctionField_app_res N i ((hVW x₀).trans hW'U) E, show
    T.presheaf.map (homOfLE ((hVW x₀).trans hW'U)).op E = e x₀ from by
      rw [← he' x₀, ← hE]
      change _ = T.presheaf.map _ (T.presheaf.map _ E)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl]
  exact he x₀ i inferInstance

/-- **Any two local generators of the adjoint of a seminormal `S₂` scheme differ by a
function.** Let `T` be a reduced, seminormal, `S₂` scheme whose normalization components are
closed immersions with distinct generic points, and `s, s'` local generators of the adjoint of
`T` on `U` (`MMP.Fourfold.IsAdjointGeneratorOn`). Then `s = ν^*e · s'` for a function `e` on
`U`: locally by `exists_local_smul_eq_of_isAdjointGeneratorOn`, and globally by gluing and
extending across codimension two (`exists_smul_eq_of_forall_exists_local`). -/
public theorem exists_smul_eq_of_isAdjointGeneratorOn {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [IsLocallyNoetherian T]
    (hS2 : SatisfiesS2 T) (hsn : IsSeminormal T) [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i))
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base)
    {n : ℕ} (hdim : ∀ i, topologicalKrullDim (N.X i) = (n : ℕ)) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (Θ i).coeff P = 1)
    {m : ℕ} {U : T.Opens} {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsAdjointGeneratorOn N n m Θ U s) (hs' : IsAdjointGeneratorOn N n m Θ U s') :
    ∃ e : Γ(T, U), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e) • s' i :=
  exists_smul_eq_of_forall_exists_local N hS2 (fun i => (hs'.1 i).1) hgen fun x hx hxd =>
    exists_local_smul_eq_of_isAdjointGeneratorOn N hsn hci hgen hdim hΘ hs hs' x hx hxd

end SdltUniqueness

end MMP.Fourfold.SdltFloor
