module

public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier

/-!
# Relative bigness is stable under adding relatively nef divisors on surfaces

Let `f : S ⟶ Z` be a morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, with `S` a normal `ℚ`-factorial surface. If `L` is an `f`-nef and `f`-big
`ℚ`-divisor and `M` is an `f`-nef `ℚ`-divisor on `S`, then `aL + bM` is `f`-big for all rationals
`a > 0` and `b ≥ 0`. In other words, the `f`-nef and `f`-big `ℚ`-divisors form a convex cone, and
adding an `f`-nef divisor to one of them keeps it `f`-big.

The proof: a Cartier multiple `D₀ = m₀ L` is `f`-big, so by the relative Kodaira decomposition
some multiple `m D₀` is linearly equivalent to `A + E` with `A` an `f`-ample and `E` an effective
Cartier divisor. Let `M₁ = n M` be a Cartier multiple of `M`. A common multiple `p (aL + bM)` is
`c₁ m D₀ + c₂ M₁` with integers `c₁ ≥ 1`, `c₂ ≥ 0`, which is linearly equivalent to
`(c₁ A + c₂ M₁) + c₁ E`. On every nonzero class of the closed relative cone of curves `A` is
positive and `M₁` is nonnegative, so `c₁ A + c₂ M₁` is `f`-ample by the relative Kleiman
criterion, and `c₁ E` is effective; the decomposition then gives `f`-bigness.

## Main results

* `MMP.Mori.QDivisor.IsRelativelyBig.smul_add_smul_of_isRelativelyNef`: the stability statement.
* `MMP.Mori.Divisor.isRelativelyBig_iff_isRelativelyBigCartier`: a Cartier Weil divisor is
  `f`-big exactly when a Cartier divisor with an isomorphic sheaf is, together with the sheaf
  comparisons `MMP.Mori.exists_sheaf_iso_divisorialSheaf`,
  `MMP.Mori.nonempty_divisorialSheaf_add_iso` and `MMP.Mori.nonempty_divisorialSheaf_nsmul_iso`.

## Implementation notes

`f`-nefness is `MMP.Mori.QDivisor.IsRelativelyNef` and `f`-bigness is
`MMP.Mori.QDivisor.IsRelativelyBig`. `ℚ`-factoriality is `MMP.Fourfold.IsQFactorial`, which
includes normality of `S`; "surface" is `topologicalKrullDim S = 2`. The field of complex numbers
is replaced by an algebraically closed field of characteristic zero.

The argument works in every relative dimension at once: it uses the relative Kodaira
decomposition `MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add` in both
directions instead of a case analysis of the generic fibre after Stein factorization.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.22–3.23
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

/-! ### Comparison of divisorial and Cartier sheaves -/

section Comparison

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- Every Cartier Weil divisor `D` has a Cartier divisor `C` with `𝒪_X(D) ≅ 𝒪_X(C)`. -/
theorem exists_sheaf_iso_divisorialSheaf {D : Divisor X} (hD : D.IsCartier) :
    ∃ C : X.CartierDivisor, Nonempty (D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C) := by
  have := hD.isInvertibleModule_divisorialSheaf
  exact MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf

omit [IsIntegral X] in
/-- If `𝒪_X(W₁) ≅ 𝒪_X(C₁)` and `𝒪_X(W₂) ≅ 𝒪_X(C₂)`, then `𝒪_X(W₁ + W₂) ≅ 𝒪_X(C₁ + C₂)`. -/
theorem nonempty_divisorialSheaf_add_iso {W₁ W₂ : Divisor X} (h₁ : W₁.IsCartier)
    (h₂ : W₂.IsCartier) {C₁ C₂ : X.CartierDivisor}
    (e₁ : W₁.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C₁)
    (e₂ : W₂.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C₂) :
    Nonempty ((W₁ + W₂).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (C₁ + C₂)) :=
  ⟨(h₁.divisorialSheafTensorIso h₂).symm ≪≫ MonoidalCategory.tensorIso e₁ e₂ ≪≫
    MMP.CartierDivisorSheaf.sheafMulIso C₁ C₂⟩

/-- If `𝒪_X(W) ≅ 𝒪_X(C)`, then `𝒪_X(n • W) ≅ 𝒪_X(n • C)` for every `n ≥ 1`. -/
theorem nonempty_divisorialSheaf_nsmul_iso {W : Divisor X} (hW : W.IsCartier)
    {C : X.CartierDivisor} (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C)
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((n • W).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (n • C)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [one_nsmul, one_nsmul]
    exact ⟨e⟩
  | succ n hn ih =>
    obtain ⟨ie⟩ := ih
    rw [succ_nsmul, succ_nsmul]
    exact nonempty_divisorialSheaf_add_iso (hW.nsmul n) hW ie e

/-- The comparison of sheaves for `W' + n W`, `n ≥ 0`. -/
private theorem nonempty_divisorialSheaf_add_nsmul_iso {W' W : Divisor X} (hW' : W'.IsCartier)
    (hW : W.IsCartier) {C' C : X.CartierDivisor}
    (e' : W'.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C')
    (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C) (n : ℕ) :
    Nonempty ((W' + n • W).divisorialSheaf ≅
      MMP.CartierDivisor.sheaf (C' + n • C)) := by
  induction n with
  | zero =>
    rw [zero_nsmul, zero_nsmul, add_zero, add_zero]
    exact ⟨e'⟩
  | succ n ih =>
    obtain ⟨ie⟩ := ih
    rw [succ_nsmul, succ_nsmul, ← add_assoc, ← add_assoc]
    exact nonempty_divisorialSheaf_add_iso (hW'.add (hW.nsmul n)) hW ie e

end Comparison

/-! ### Bigness of Weil and Cartier divisors -/

section Big

/-- The generic rank only depends on the isomorphism class of the module. -/
theorem relativeGenericRank_congr {X Y : Scheme.{0}} (f : X ⟶ Y) [IrreducibleSpace X]
    {F G : X.Modules} (e : F ≅ G) : relativeGenericRank f F = relativeGenericRank f G :=
  Scheme.Modules.fiberRank_eq_of_iso ((Scheme.Modules.pushforward f).mapIso e) _

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (f : X ⟶ Y) {D : Divisor X} (hD : D.IsCartier) {C : X.CartierDivisor}
  (e : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C)

include hD e

/-- If `𝒪_X(D) ≅ 𝒪_X(C)`, then `𝒪_X(mD)` and `𝒪_X(mC)` have the same generic rank for `m ≥ 1`. -/
private theorem relativeGenericRank_zsmul_eq {m : ℤ} (hm : 1 ≤ m) :
    relativeGenericRank f (m • D).divisorialSheaf =
      relativeGenericRank f (MMP.CartierDivisor.sheaf (m • C)) := by
  lift m to ℕ using by omega
  obtain ⟨ie⟩ := nonempty_divisorialSheaf_nsmul_iso hD e m (by omega)
  simpa only [natCast_zsmul] using relativeGenericRank_congr f ie

/-- A Cartier Weil divisor `D` is `f`-big exactly when a Cartier divisor `C` with
`𝒪_X(D) ≅ 𝒪_X(C)` is. -/
theorem Divisor.isRelativelyBig_iff_isRelativelyBigCartier :
    D.IsRelativelyBig f ↔ IsRelativelyBigCartier f C := by
  constructor <;> rintro ⟨a, b, ha, hb, c, hc, k₀, hk⟩ <;>
    refine ⟨a, b, ha, hb, c, hc, max k₀ 1, fun m hm => ?_⟩
  · rw [← relativeGenericRank_zsmul_eq f hD e (le_of_max_le_right hm)]
    exact hk m (le_of_max_le_left hm)
  · rw [relativeGenericRank_zsmul_eq f hD e (le_of_max_le_right hm)]
    exact hk m (le_of_max_le_left hm)

end Big

/-! ### Degree forms on `N₁(X/Y)` -/

section Degree

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

/-- The intersection form of `E` on `N₁(X/Y)` is the degree form of `𝒪_X(E)`. -/
private theorem intersectionNumber_ofCartier_eq_degree (E : X.CartierDivisor) :
    RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f)
        (KCartierDivisor.ofCartier ℝ E) =
      RelativeNumericalCurveClasses.degree sX f (MMP.CartierDivisor.sheaf E) :=
  Submodule.linearMap_qext _
    (LinearMap.ext fun Z => OneCycle.intersectionNumber_ofCartier (Z : OneCycle ℝ sX) E)

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree k (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree k (MMP.CartierDivisor.sheaf E) +
        C.degree k (MMP.CartierDivisor.sheaf E') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso k sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- `deg_C 𝒪_X(n E) = n · deg_C 𝒪_X(E)` along a proper curve. -/
private theorem degree_cartierSheaf_nsmul (C : ProperCurve sX) (E : X.CartierDivisor) (n : ℕ) :
    C.degree k (MMP.CartierDivisor.sheaf (n • E)) =
      n * C.degree k (MMP.CartierDivisor.sheaf E) := by
  induction n with
  | zero =>
    have h := degree_cartierSheaf_add (k := k) C 0 0
    rw [add_zero] at h
    rw [zero_nsmul]
    push_cast
    linarith
  | succ n ih =>
    rw [succ_nsmul, degree_cartierSheaf_add, ih]
    push_cast
    ring

/-- The degree form on `N₁(X/Y)` is determined by the degrees on curves. -/
private theorem degree_eq_smul_add_smul (L L₁ L₂ : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₂] (a b : ℝ)
    (h : ∀ C : ProperCurve sX,
      (C.degree k L : ℝ) = a * C.degree k L₁ + b * C.degree k L₂) :
    RelativeNumericalCurveClasses.degree sX f L =
      a • RelativeNumericalCurveClasses.degree sX f L₁ +
        b • RelativeNumericalCurveClasses.degree sX f L₂ := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  change OneCycle.degree ℝ sX L (Z : OneCycle ℝ sX) =
    a * OneCycle.degree ℝ sX L₁ (Z : OneCycle ℝ sX) +
      b * OneCycle.degree ℝ sX L₂ (Z : OneCycle ℝ sX)
  simp only [OneCycle.degree_apply, h, Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun C _ => by ring

/-- A sheaf of nonnegative degree on every contracted curve has a degree form that is
nonnegative on the closed relative cone of curves. -/
private theorem degree_nonneg_of_forall (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ C.degree k L)
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    0 ≤ RelativeNumericalCurveClasses.degree sX f L z := by
  have hS : IsClosed {z : RelativeNumericalCurveClasses sX f |
      0 ≤ RelativeNumericalCurveClasses.degree sX f L z} :=
    isClosed_le continuous_const (RelativeNumericalCurveClasses.continuous_degree sX f _)
  refine closure_minimal (fun w hw => ?_) hS hz
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    change 0 ≤ OneCycle.degree ℝ sX _ (C.cycle ℝ)
    rw [OneCycle.degree_cycle]
    exact_mod_cast h C hC
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    exact add_nonneg hx hy
  | smul a x _ hx =>
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
    exact mul_nonneg a.2 hx

end Degree

/-- A nonnegative rational `a` satisfies `α = a * β` for naturals `α`, `β` with `0 < β`, and
`0 < α` when `0 < a`. -/
private theorem exists_nat_eq_mul {a : ℚ} (ha : 0 ≤ a) :
    ∃ α β : ℕ, 0 < β ∧ (α : ℚ) = a * β ∧ (0 < a → 0 < α) := by
  have hnum : (0 : ℤ) ≤ a.num := Rat.num_nonneg.mpr ha
  refine ⟨a.num.toNat, a.den, a.den_pos, ?_, fun h => ?_⟩
  · rw [show ((a.num.toNat : ℕ) : ℚ) = ((a.num.toNat : ℤ) : ℚ) by norm_cast,
      Int.toNat_of_nonneg hnum, Rat.mul_den_eq_num]
  · have := Rat.num_pos.mpr h
    omega

/-- If `M₁ = n M` is a Cartier multiple of an `f`-nef `ℚ`-divisor `M` and `𝒪_X(M₁) ≅ 𝒪_X(N)`,
then `𝒪_X(N)` has nonnegative degree on every curve contracted by `f`. -/
private theorem degree_cartierSheaf_nonneg_of_isRelativelyNef {k : Type} [Field k]
    {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {f : X ⟶ Y} {M : QDivisor X} (hM : M.IsRelativelyNef sX f) {n : ℕ}
    (hn : 0 < n) {M₁ : Divisor X} (hM₁c : M₁.IsCartier)
    (hM₁M : Divisor.toQDivisor M₁ = (n : ℤ) • M) {N : X.CartierDivisor}
    (e : M₁.divisorialSheaf ≅ MMP.CartierDivisor.sheaf N)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 ≤ C.degree k (MMP.CartierDivisor.sheaf N) := by
  have h := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hM hM.fst C hC
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le M hM.fst hn M₁ hM₁c hM₁M] at h
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hM₁c.isInvertibleModule_divisorialSheaf
  unfold ProperCurve.degree
  rw [← degreeOn_eq_of_iso k sX C.ι C.dim_le e]
  exact_mod_cast (by simpa using (le_div_iff₀ (by positivity : (0 : ℚ) < n)).1 h :
    (0 : ℚ) ≤ M₁.degreeOn k sX C.ι C.dim_le hM₁c)

/-- **Ample plus nef is ample, relative Kleiman form.** If `A` is `f`-ample and `𝒪_X(N)` has
nonnegative degree on every curve contracted by `f`, then `c₁ A + c₂ N` is `f`-ample for
`c₁ ≥ 1`, `c₂ ≥ 0`. -/
private theorem isRelativelyAmple_nsmul_add_nsmul {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [MMP.Mori.IsVariety k sX] [MMP.Mori.IsVariety k sY] {f : X ⟶ Y} (hfp : IsProjective f)
    (hf : f ≫ sY = sX)
    {A N : X.CartierDivisor} (hA : IsRelativelyAmple f (MMP.CartierDivisor.sheaf A))
    (hN : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ C.degree k (MMP.CartierDivisor.sheaf N))
    {c₁ : ℕ} (hc₁ : 1 ≤ c₁) (c₂ : ℕ) :
    IsRelativelyAmple f (MMP.CartierDivisor.sheaf (c₁ • A + c₂ • N)) := by
  have kleiman := isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sY sX f
    hfp hf
  refine (kleiman _).2 fun z hz hz0 => ?_
  have hAz := (kleiman A).1 hA z hz hz0
  rw [intersectionNumber_ofCartier_eq_degree] at hAz ⊢
  rw [degree_eq_smul_add_smul (f := f) _ (MMP.CartierDivisor.sheaf A)
    (MMP.CartierDivisor.sheaf N) (c₁ : ℝ) (c₂ : ℝ) fun C => by
      rw [degree_cartierSheaf_add, degree_cartierSheaf_nsmul, degree_cartierSheaf_nsmul]
      push_cast
      ring]
  have hNz := degree_nonneg_of_forall (f := f) _ hN hz
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hc₁' : (0 : ℝ) < c₁ := by exact_mod_cast hc₁
  positivity

/-- **Relative bigness plus a relatively nef divisor on a surface.** Let `f : S ⟶ Z` be a morphism
of projective varieties over an algebraically closed field `k` of characteristic zero, with `S` a
normal `ℚ`-factorial surface. If the `ℚ`-divisor `L` is `f`-nef and `f`-big and the `ℚ`-divisor
`M` is `f`-nef, then `a • L + b • M` is `f`-big for all rationals `a > 0` and `b ≥ 0`. -/
@[mmp "lem_mmp_surface_relative_nef_big_convexity"]
theorem QDivisor.IsRelativelyBig.smul_add_smul_of_isRelativelyNef {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {S Z : Scheme.{0}} (sS : S ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [IsProjectiveVariety k sS] [IsProjectiveVariety k sZ]
    [IsLocallyNoetherian S] [IsNormal S] (hS : MMP.Fourfold.IsQFactorial sS)
    (hdim : topologicalKrullDim S = 2) (f : S ⟶ Z) (hf : f ≫ sZ = sS) {L M : QDivisor S}
    (hLn : L.IsRelativelyNef sS f) (hLb : L.IsRelativelyBig f) (hMn : M.IsRelativelyNef sS f)
    {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) :
    (a • L + b • M).IsRelativelyBig f := by
  have hSp : MMP.Mori.IsProjectiveVariety k sS := ‹_›
  have hZp : MMP.Mori.IsProjectiveVariety k sZ := ‹_›
  have := hSp.toIsVariety
  have := hZp.toIsVariety
  have : IsSeparated sZ := hZp.toIsVariety.toIsSeparated
  have hfp : IsProjective f := IsProjective.of_comp f sZ (hf ▸ hSp.isProjective.isProjective)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨m₀, hm₀, D₀, hD₀L, hD₀c, hD₀b⟩ := hLb
  obtain ⟨Ec, ⟨e₀⟩⟩ := exists_sheaf_iso_divisorialSheaf hD₀c
  obtain ⟨m, hm, A, E, hA, hE, hlin⟩ :=
    (isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sS sZ f hf Ec).1
      ((Divisor.isRelativelyBig_iff_isRelativelyBigCartier f hD₀c e₀).1 hD₀b)
  obtain ⟨n, hn, M₁, hM₁M, hM₁c⟩ := hMn.fst.exists_pos
  obtain ⟨M₁c, ⟨e₁⟩⟩ := exists_sheaf_iso_divisorialSheaf hM₁c
  obtain ⟨α, β, hβ, hαβ, hα⟩ := exists_nat_eq_mul ha.le
  obtain ⟨γ, δ, hδ, hγδ, -⟩ := exists_nat_eq_mul hb
  set c₁ : ℕ := n * δ * α with hc₁def
  set c₂ : ℕ := m₀ * β * γ * m with hc₂def
  have hc₁ : 1 ≤ c₁ := Nat.mul_pos (Nat.mul_pos hn hδ) (hα ha)
  set G : Divisor S := (c₁ * m) • D₀ + c₂ • M₁ with hGdef
  set Gc : S.CartierDivisor := (c₁ * m) • Ec + c₂ • M₁c with hGcdef
  have hGc : G.IsCartier := (hD₀c.nsmul _).add (hM₁c.nsmul _)
  obtain ⟨eG⟩ : Nonempty (G.divisorialSheaf ≅ MMP.CartierDivisor.sheaf Gc) := by
    obtain ⟨e⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀c e₀ (c₁ * m) (Nat.mul_pos hc₁ hm)
    exact nonempty_divisorialSheaf_add_nsmul_iso (hD₀c.nsmul _) hM₁c e e₁ c₂
  have hbig : IsRelativelyBigCartier f Gc := by
    refine (isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sS sZ f hf Gc).2
      ⟨1, one_pos, c₁ • A + c₂ • M₁c, c₁ • E,
        isRelativelyAmple_nsmul_add_nsmul sS sZ hfp hf hA
          (degree_cartierSheaf_nonneg_of_isRelativelyNef sS hMn hn hM₁c hM₁M e₁) hc₁ c₂,
        hE.nsmul c₁, ?_⟩
    change 1 • Gc - (c₁ • A + c₂ • M₁c + c₁ • E) ∈ MMP.Intersection.principalSubgroup S
    convert AddSubgroup.nsmul_mem _ hlin c₁ using 1
    rw [hGcdef, one_nsmul, mul_nsmul', nsmul_sub, nsmul_add]
    abel
  refine ⟨m₀ * n * β * δ * m, by positivity, G, ?_, hGc,
    (Divisor.isRelativelyBig_iff_isRelativelyBigCartier f hGc eG).2 hbig⟩
  rw [hGdef, map_add, map_nsmul, map_nsmul, hD₀L, hM₁M]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, hc₁def, hc₂def]
  push_cast
  rw [hαβ, hγδ]
  module

end MMP.Mori
