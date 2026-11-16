module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripTestDivisorAmple
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
public import MMP.AlgebraicGeometry.Positivity.AmpleAdjunctionRestriction

@[expose] public section

section

/-!
# In the strip, the restricted Euler characteristic is the number of sections

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, `(j₀, c)` a tie-breaker of a
`(p, q)`-adapted resolution `f : Y ⟶ X` with test boundary `A'`, `F = F_{j₀}` with closed
immersion `ι : F ⟶ Y`, and `p', q'` integers with `p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and
`aq' - rp' ≤ aq - rp`. Write `B' = f^*(p'H + q'a(K_X + Δ)) = p' H' + q' B''` and let `H_F`, `B_F`
be divisors on `F` with `𝒪_F(H_F) ≅ ι^* 𝒪_Y(H')`, `𝒪_F(B_F) ≅ ι^* 𝒪_Y(B'')`, so that
`P_F = p' H_F + q' B_F` satisfies `𝒪_F(P_F) ≅ ι^* 𝒪_Y(B')`.

The test divisor `B' + A' - F - K_Y` is ample, so its adjoint restriction `P_F + A'|_F - K_F`
is ample on `F`. The support of `A'|_F` is snc, and Kawamata–Viehweg vanishing for the round-up
on `F` kills `Hⁱ(F, 𝒪_F(P_F + ⌈A'|_F⌉))` for `i > 0`. So the Euler characteristic of
`𝒪_F(P_F + ⌈A'|_F⌉)` is its `h⁰`, and since `⌈A'|_F⌉ = ⌈A'⌉|_F`, the sheaf
`𝒪_F(P_F + ⌈A'|_F⌉)` is `ι^* 𝒪_Y(B' + ⌈A'⌉)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4 Step 9
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bStripRestrictedEulerEqualsH0Proof

section Restricts

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {F : MMP.Mori.PrimeDivisor Y} [IsLocallyNoetherian F.idealSheaf.subscheme]
  [IsNormal F.idealSheaf.subscheme] [CompactSpace F.idealSheaf.subscheme]

/-- `E ↝ E'`: the divisorial sheaf of `E'` on `F` is the restriction of that of `E`. -/
private def Restricts (F : MMP.Mori.PrimeDivisor Y) [IsLocallyNoetherian F.idealSheaf.subscheme]
    [IsNormal F.idealSheaf.subscheme] (E : Divisor Y) (E' : Divisor F.idealSheaf.subscheme) :
    Prop :=
  Nonempty (E'.divisorialSheaf ≅
    (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj E.divisorialSheaf)

/-- `ι^*` is additive: if `a ↝ a'` and `b ↝ b'`, then `a + b ↝ a' + b'`. -/
private theorem Restricts.add (hY : ∀ D : Divisor Y, D.IsCartier)
    (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier) {a b : Divisor Y}
    {a' b' : Divisor F.idealSheaf.subscheme} (ha : Restricts F a a') (hb : Restricts F b b') :
    Restricts F (a + b) (a' + b') := by
  obtain ⟨ea⟩ := ha
  obtain ⟨eb⟩ := hb
  exact ⟨((hF a').divisorialSheafTensorIso (hF b')).symm ≪≫
    MonoidalCategory.tensorIso ea eb ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorModulesIso F.idealSheaf.subschemeι _ _).symm ≪≫
    (Scheme.Modules.pullback F.idealSheaf.subschemeι).mapIso
      ((hY a).divisorialSheafTensorIso (hY b))⟩

/-- Cancellation: if `a + b ↝ c'` and `a ↝ a'`, then `b ↝ c' - a'`. -/
private theorem Restricts.cancel [IsIntegral F.idealSheaf.subscheme]
    (hY : ∀ D : Divisor Y, D.IsCartier) (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier)
    (hinv : ∀ L : F.idealSheaf.subscheme.Modules,
      Stacks.Ample.IsInvertibleModule F.idealSheaf.subscheme L →
        ∃ G : Divisor F.idealSheaf.subscheme, Nonempty (G.divisorialSheaf ≅ L))
    {a b : Divisor Y} {a' c' : Divisor F.idealSheaf.subscheme}
    (h : Restricts F (a + b) c') (ha : Restricts F a a') : Restricts F b (c' - a') := by
  haveI := (hY b).isInvertibleModule_divisorialSheaf
  obtain ⟨G, ⟨eG⟩⟩ := hinv ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj b.divisorialSheaf)
    inferInstance
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := Restricts.add hY hF ha ⟨eG⟩
  have hl : c'.LinearlyEquivalent (a' + G) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ e'.symm)
  have hl' : (c' - a').LinearlyEquivalent G := by
    have := hl.add (Divisor.LinearlyEquivalent.refl (-a'))
    rwa [← sub_eq_add_neg, add_neg_cancel_comm] at this
  exact ⟨hl'.divisorialSheafIso ≪≫ eG⟩

/-- `ι^*` respects integer multiples: if `a ↝ a'` then `n • a ↝ n • a'` for `n ∈ ℤ`. -/
private theorem Restricts.zsmul [IsIntegral F.idealSheaf.subscheme]
    (hY : ∀ D : Divisor Y, D.IsCartier) (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier)
    (hinv : ∀ L : F.idealSheaf.subscheme.Modules,
      Stacks.Ample.IsInvertibleModule F.idealSheaf.subscheme L →
        ∃ G : Divisor F.idealSheaf.subscheme, Nonempty (G.divisorialSheaf ≅ L))
    (h0 : Restricts F 0 0) {a : Divisor Y} {a' : Divisor F.idealSheaf.subscheme}
    (ha : Restricts F a a') (n : ℤ) : Restricts F (n • a) (n • a') := by
  have hnat : ∀ m : ℕ, Restricts F ((m : ℤ) • a) ((m : ℤ) • a') := by
    intro m
    induction m with
    | zero => simpa using h0
    | succ m ih => simpa [add_smul] using ih.add hY hF ha
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact hnat m
  · have h := Restricts.cancel hY hF hinv (b := -((m : ℤ) • a)) (c' := 0)
      (by simpa using h0) (hnat m)
    simpa [neg_smul] using h

end Restricts

/-- The support of an integer multiple is contained in the support. -/
private theorem supp_zsmul_le {X : Scheme.{0}} (D : Divisor X) (m : ℤ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨E, hE, hx⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, fun h0 => hE ?_, hx⟩
  rw [DivisorWithCoeffs.coeff_smul, h0, smul_zero]

/-- The round-down of a `ℚ`-divisor with integral coefficients is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{0}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D := by
  ext E
  change ((Divisor.toQDivisor D).roundDown).coeff E = D.coeff E
  rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]

/-- For integral `B, K` and a `ℚ`-divisor `A`, `K + ⌈(B - K) + A⌉ = B + ⌈A⌉`. -/
private theorem add_roundUp_toQDivisor_sub_add {X : Scheme.{0}} (B KX : Divisor X)
    (A : QDivisor X) : KX + (Divisor.toQDivisor (B - KX) + A).roundUp = B + A.roundUp := by
  ext P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
    Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub]
  rw [Int.ceil_intCast_add]
  ring

/-- For a rationality datum, a pull-back of the integral divisor `p'H + q'a(K_X + Δ)` is a
pull-back of the `ℚ`-divisor `p'H + q'a(K_X + Δ)`. -/
private theorem isPullback_toQDivisor_stripDivisor {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H) {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {p' q' : ℤ}
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hB B') :
    ∃ hb, (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).IsPullback f hb
      (Divisor.toQDivisor B') := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hr0 : (a • (Divisor.toQDivisor K + Δ)).roundDown = D₀ := by
    rw [← hD₀, roundDown_toQDivisor]
  have hMQ : Divisor.toQDivisor (stripDivisor K Δ a H p' q') =
      p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ) := by
    rw [stripDivisor, hr0, map_add, map_zsmul, map_zsmul, hD₀, smul_smul]
  rw [← hMQ]
  refine ⟨_, QDivisor.isPullback_toQDivisor ?_
    (fun Z hZ => hB Z (by rwa [Divisor.supp_toQDivisor] at hZ)) hB'⟩
  rw [stripDivisor, hr0]
  exact (h.isCartier_H.zsmul p').add (hD₀c.zsmul q')

/-- For a rationality datum, the pull-back of `p'H + q'⌊a(K_X + Δ)⌋` is `p'H' + q'B''`, where
`H'` and `B''` are the pull-backs of `H` and `⌊a(K_X + Δ)⌋`. -/
private theorem eq_add_of_isPullback_stripDivisor {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H) {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {p' q' : ℤ}
    {hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {H' : Divisor Y} (hH' : H.IsPullback f hHf H')
    {hBf : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp}
    {B'' : Divisor Y} (hB'' : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsPullback f hBf B'')
    {hM : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hM B') :
    B' = p' • H' + q' • B'' := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hDc : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsCartier := by
    rwa [← hD₀, roundDown_toQDivisor]
  have hHc := h.isCartier_H
  exact hB'.eq ((hHc.zsmul p').add (hDc.zsmul q')) <| Divisor.IsPullback.add (hHc.zsmul p')
    (hDc.zsmul q') hM (hH'.zsmul hHc p' fun Z hZ => hHf Z (supp_zsmul_le H p' hZ))
    (hB''.zsmul hDc q' fun Z hZ => hBf Z (supp_zsmul_le _ q' hZ))

/-- A divisor supported on the components `F_j` of an adapted resolution is snc. -/
private theorem isSNC_of_forall_exists_eq {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R Y) (hD : ∀ E, D.coeff E ≠ 0 → ∃ j, F j = E) :
    D.IsSNC (f ≫ sX) := by
  classical
  refine h.isSNC.of_support_subset fun E hE => ?_
  obtain ⟨j, rfl⟩ := hD E (Finsupp.mem_support_iff.mp hE)
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finset.sum_eq_single j
    (fun b _ hb => Finsupp.single_eq_of_ne' (h.injective.ne hb)) (by simp)]
  simp

/-- `F_{j₀} + D` is snc for a divisor `D` supported on the components `F_j`. -/
private theorem isSNC_single_add {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) {R : Type*}
    [AddCommMonoidWithOne R] (j₀ : Fin s) (D : DivisorWithCoeffs R Y)
    (hD : ∀ E, D.coeff E ≠ 0 → ∃ j, F j = E) :
    DivisorWithCoeffs.IsSNC (f ≫ sX) (Finsupp.single (F j₀) (1 : R) + D) := by
  refine isSNC_of_forall_exists_eq h _ fun E hE => ?_
  by_cases hE0 : F j₀ = E
  · exact ⟨j₀, hE0⟩
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff, Finsupp.single_eq_of_ne' hE0,
      zero_add] at hE
    exact hD E hE

/-- The coefficients of the test boundary `A' = ∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j`. -/
private theorem exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero {Y : Scheme.{0}} {s : ℕ}
    {F : Fin s → MMP.Mori.PrimeDivisor Y} (r aj pj : Fin s → ℚ)
    (j₀ : Fin s) (c : ℚ) {E : MMP.Mori.PrimeDivisor Y}
    (hE : (tieBreakerBoundary F r aj pj j₀ c).coeff E ≠ 0) : ∃ j, j ≠ j₀ ∧ F j = E := by
  classical
  rw [tieBreakerBoundary, DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply] at hE
  obtain ⟨j, hj, hjE⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
  refine ⟨j, (Finset.mem_erase.mp hj).1, ?_⟩
  by_contra hne
  exact hjE (Finsupp.single_eq_of_ne' hne)

/-- The test boundary has coefficient `0` along `F_{j₀}`. -/
private theorem coeff_tieBreakerBoundary_self {Y : Scheme.{0}} {s : ℕ}
    {F : Fin s → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F) (r aj pj : Fin s → ℚ)
    (j₀ : Fin s) (c : ℚ) : (tieBreakerBoundary F r aj pj j₀ c).coeff (F j₀) = 0 := by
  by_contra hne
  obtain ⟨j, hj, hjE⟩ := exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero r aj pj j₀ c hne
  exact hj (hF hjE)

/-- If `d ≠ ⊥` and `d + 1 = n`, then `n = m + 1` and `d = m` for some `m : ℕ`. -/
private theorem exists_eq_add_one_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (hd : d ≠ ⊥)
    (h : d + 1 = n) : ∃ m : ℕ, n = m + 1 ∧ d = m := by
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  induction e with
  | top =>
    have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) = n := by exact_mod_cast h
    simp at h'
  | coe e =>
    have h' : e + 1 = n := by exact_mod_cast h
    exact ⟨e, h'.symm, rfl⟩

/-- A prime divisor of an integral scheme of finite type of dimension `n` over a field has
dimension `n - 1`, and `n ≥ 1`. -/
private theorem exists_topologicalKrullDim_subscheme_eq {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} (hdim : topologicalKrullDim Y = n)
    (F : MMP.Mori.PrimeDivisor Y) :
    ∃ m : ℕ, n = m + 1 ∧ topologicalKrullDim F.idealSheaf.subscheme = m := by
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY F.genericPoint
  rw [F.coheight_genericPoint, hdim, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    ← MMP.Mori.topologicalKrullDim_subscheme_eq] at h1
  refine exists_eq_add_one_of_add_one_eq ?_ (by exact_mod_cast h1)
  rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
  haveI := F.integral
  infer_instance

/-- The prime divisors `F_j` of an adapted resolution are smooth. -/
private theorem isSmoothScheme_subschemeι_comp {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) (j₀ : Fin s) :
    IsSmoothScheme ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) := by
  classical
  refine h.isSNC.1 (F j₀) ?_
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, h.injective.eq_iff]

/-- The coefficients of the restriction of `∑_{j ∈ s} γ_j F_j` to a prime divisor `F_{j'}`
(`j' ∉ s`, the `F_j` distinct) are `∑_{j ∈ s} (F_j · Q) γ_j`. -/
private theorem coeff_restrictPrimeDivisor_sum_single {Y : Scheme.{0}} {ι : Type*}
    [IsLocallyNoetherian Y] [CompactSpace Y]
    {R : Type*} [AddCommMonoid R] (F : ι → MMP.Mori.PrimeDivisor Y) (hF : Function.Injective F)
    (s : Finset ι) {j' : ι} (hj' : j' ∉ s) (γ : ι → R)
    (Q : MMP.Mori.PrimeDivisor (F j').idealSheaf.subscheme) :
    (DivisorWithCoeffs.restrictPrimeDivisor (∑ j ∈ s, Finsupp.single (F j) (γ j)) (F j')).coeff
        Q = ∑ j ∈ s, (F j).intersectionLength (F j').idealSheaf.subschemeι Q • γ j := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  have h0 : DivisorWithCoeffs.coeff (∑ j ∈ s, Finsupp.single (F j) (γ j)) (F j') = 0 := by
    rw [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hj' (hF h ▸ hj)
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ h0,
    ← Finsupp.sum_finset_sum_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (smul_zero _)

/-- The restriction `A'|_{F_{j₀}}` of the test boundary is snc on `F_{j₀}`: its support lies in
that of `(∑_{j ≠ j₀} F_j)|_{F_{j₀}}`, which is snc because `∑_j F_j` is. -/
private theorem isSNC_restrictPrimeDivisor_tieBreakerBoundary {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} [AlgebraicGeometry.IsVariety k (f ≫ sX)] [Smooth (f ≫ sX)]
    {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) (r : Fin s → ℚ) (j₀ : Fin s)
    (c : ℚ) : ((tieBreakerBoundary F r aj pj j₀ c).restrictPrimeDivisor (F j₀)).IsSNC
      ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) := by
  classical
  set S := Finset.univ.erase j₀
  have hj₀ : j₀ ∉ S := Finset.notMem_erase j₀ _
  have hFD : F j₀ ∉ S.image F := fun hm => by
    obtain ⟨j, hj, hjF⟩ := Finset.mem_image.mp hm
    exact hj₀ (h.injective hjF ▸ hj)
  have hsnc := isSNC_single_add h j₀ (∑ E ∈ S.image F, Finsupp.single E (1 : ℤ)) fun E hE => by
    rw [DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply] at hE
    obtain ⟨E', hE', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hE'
    exact ⟨j, (Finsupp.single_apply_ne_zero.mp hne).1.symm⟩
  obtain ⟨hsncT, -⟩ :=
    DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single (f ≫ sX) (F j₀) _ hFD hsnc
  rw [Finset.sum_image fun _ _ _ _ he => h.injective he] at hsncT
  refine hsncT.of_support_subset fun Q hQ => ?_
  rw [Finsupp.mem_support_iff] at hQ ⊢
  change DivisorWithCoeffs.coeff _ Q ≠ 0 at hQ
  change DivisorWithCoeffs.coeff _ Q ≠ 0
  rw [tieBreakerBoundary, coeff_restrictPrimeDivisor_sum_single F h.injective S hj₀] at hQ
  rw [coeff_restrictPrimeDivisor_sum_single F h.injective S hj₀]
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hl : (F j).intersectionLength (F j₀).idealSheaf.subschemeι Q ≠ 0 := fun h0 =>
    hne (by rw [h0, zero_smul])
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨j, hj, Nat.pos_of_ne_zero hl⟩).ne'

/-- The round-up of the test boundary commutes with restriction to `F_{j₀}`:
`⌈A'|_{F_{j₀}}⌉ = ⌈A'⌉|_{F_{j₀}}`, since `F_{j₀} + A'` is snc and `F_{j₀}` is not a component of
`A'`. -/
private theorem roundUp_restrictPrimeDivisor_tieBreakerBoundary {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} [AlgebraicGeometry.IsVariety k (f ≫ sX)]
    (hsm : IsSmoothScheme (f ≫ sX)) {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) (r : Fin s → ℚ) (j₀ : Fin s)
    (c : ℚ) (hsmF : IsSmoothScheme ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX))
    (hc0 : (0 : Divisor Y).IsCartier) :
    ((tieBreakerBoundary F r aj pj j₀ c).restrictPrimeDivisor (F j₀)).roundUp =
      (tieBreakerBoundary F r aj pj j₀ c).roundUp.restrictPrimeDivisor (F j₀) := by
  have hLF : ¬ ((F j₀).support : Set Y) ⊆ ((0 : Divisor Y).supp : Set Y) := by
    rw [DivisorWithCoeffs.supp_zero]
    intro hsub
    exact hsub (a := (F j₀).genericPoint) (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
  have key := DivisorWithCoeffs.restrictPrimeDivisor_roundUp (f ≫ sX) (R := ℚ) inferInstance
    hsm (F j₀) hsmF 0 hc0 hLF _ (coeff_tieBreakerBoundary_self h.injective r aj pj j₀ c)
    (isSNC_single_add h j₀ _ fun E hE =>
      (exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero r aj pj j₀ c hE).imp
      fun _ => And.right)
  rw [map_zero, zero_add] at key
  exact key.symm

/-- **Kawamata–Viehweg vanishing for an ample adjoint divisor.** On a smooth projective variety
`Z` with canonical divisor `K_Z`, let `P` be a divisor and `A` an snc `ℚ`-divisor with
`P + A - K_Z` ample. Then `Hʲ(Z, 𝒪_Z(P + ⌈A⌉)) = 0` for `j ≠ 0`. -/
private theorem finrank_cohomologyOverField_add_roundUp_eq_zero {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k sZ] (hsm : IsSmoothScheme sZ)
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] [QuasiCompact sZ] {n : ℕ}
    {KZ : Divisor Z} (hK : KZ.IsCanonicalDivisor sZ n) (P : Divisor Z) {A : QDivisor Z}
    (hA : A.IsSNC sZ) (hamp : (Divisor.toQDivisor P + A - Divisor.toQDivisor KZ).IsAmple)
    (j : ℕ) (hj : j ≠ 0) :
    Module.finrank k (cohomologyOverField k sZ (P + A.roundUp).divisorialSheaf j) = 0 := by
  rw [show Divisor.toQDivisor P + A - Divisor.toQDivisor KZ = Divisor.toQDivisor (P - KZ) + A by
    rw [map_sub]; abel] at hamp
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple sZ hamp
  have hKV := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    sZ hsm hK (P - KZ) A hA hnef hbig j (by omega)
  rw [add_roundUp_toQDivisor_sub_add] at hKV
  haveI := (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k sZ
    (P + A.roundUp).divisorialSheaf j).toEquiv.subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- The restriction of the zero divisor to a prime divisor is zero. -/
private theorem restrictPrimeDivisor_zero {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    [CompactSpace Y] (F : MMP.Mori.PrimeDivisor Y) :
    (0 : Divisor Y).restrictPrimeDivisor F = 0 := by
  have h := DivisorWithCoeffs.restrictPrimeDivisor_zsmul (0 : Divisor Y) F (by simp) 0
  rwa [zero_smul, zero_smul] at h

/-- If the higher cohomology of `𝒪_Z(u₁D₁ + u₂D₂ + ⌈A⌉)` vanishes, its Euler characteristic
function at `(u₁, u₂)` is `h⁰` of any sheaf isomorphic to it. -/
private theorem eulerPolynomial_pair_eq_finrank {k : Type} [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsLocallyNoetherian Z] [IsNormal Z] (D₁ D₂ : Divisor Z)
    (A : QDivisor Z) (u₁ u₂ : ℤ) {G : Z.Modules}
    (e : (u₁ • D₁ + u₂ • D₂ + A.roundUp).divisorialSheaf ≅ G)
    (hvan : ∀ j : ℕ, j ≠ 0 → Module.finrank k
      (cohomologyOverField k sZ (u₁ • D₁ + u₂ • D₂ + A.roundUp).divisorialSheaf j) = 0) :
    Divisor.eulerPolynomial k sZ ![D₁, D₂] A ![u₁, u₂] =
      (Module.finrank k (cohomologyOverField k sZ G 0) : ℤ) := by
  rw [Divisor.eulerPolynomial, show ∑ i, ![u₁, u₂] i • ![D₁, D₂] i = u₁ • D₁ + u₂ • D₂ by
      simp [Fin.sum_univ_two],
    finsum_eq_single _ 0 (fun j hj => by rw [hvan j hj]; simp), pow_zero, one_mul,
    (cohomologyOverFieldIso k sZ e 0).toLinearEquiv.finrank_eq]

end MMP.FourfoldProofs.Km3bStripRestrictedEulerEqualsH0Proof

end

section

/-!
# In the strip, the restricted Euler characteristic is the number of sections

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, let `p, q > 0` be integers with `aq - rp > 0`, let `(j₀, c)` be a tie-breaker of a
`(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` with test boundary
`A' = ∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j`, and put `F = F_{j₀}`. Let `Q` be the Euler
characteristic function of `(F; f^*H|_F, f^*(a(K_X + Δ))|_F; A'|_F)`. For integers `p', q'` with
`p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `aq' - rp' ≤ aq - rp`,
`Q(p', q') = h⁰(F, 𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)|_F)`.
Indeed `(f^*M')|_F + A'|_F - K_F` is numerically equivalent to the ample divisor `N(p', q')|_F`,
hence ample, the support of `A'|_F` is snc so that `⌈A'|_F⌉ = ⌈A'⌉|_F`, and Kawamata–Viehweg
vanishing on `F` kills the higher cohomology.

## Main results

* `MMP.Mori.IsStripTieBreaker.eulerPolynomial_restrict_eq_finrank`: the statement above.

## Implementation notes

The prime divisor `F = F_{j₀}` is the integral closed subscheme `(F j₀).idealSheaf.subscheme`
with inclusion `ι = (F j₀).idealSheaf.subschemeι`, a scheme over `k` through `ι ≫ f ≫ sX`.
Since `F` may be a component of the pull-backs of `H` and of `a(K_X + Δ)`, the restrictions
`f^*H|_F` and `f^*(a(K_X + Δ))|_F` are taken as line bundles: they are any divisors `H_F` and
`B_F` on `F` with `𝒪_F(H_F) ≅ ι^* 𝒪_Y(f^*H)` and `𝒪_F(B_F) ≅ ι^* 𝒪_Y(f^*⌊a(K_X + Δ)⌋)`, and the
statement holds for every such choice. The test boundary has coefficient `0` along `F`, so
`A'|_F` is the divisor restriction `MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`. The divisor
`f^*(p'H + q'a(K_X + Δ))` on the right is any pull-back `B'` of
`MMP.Mori.stripDivisor K Δ a H p' q'`, and `𝒪_Y(B' + ⌈A'⌉)|_F` is the pull-back of its divisorial
sheaf along `ι`. The inequalities `p' ≥ (1 + c) p` and `q' ≥ (1 + c) q` are read in `ℚ`, and
`aq' - rp' ≤ aq - rp` in `ℝ`. The ground field is algebraically closed of characteristic zero, as
Kawamata–Viehweg vanishing requires.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bStripRestrictedEulerEqualsH0Proof in
/-- **In the strip, the restricted Euler characteristic is `h⁰`** (Kollár–Mori 3.4, Step 9).
Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, `p, q > 0` integers with `0 < aq - rp`, `(j₀, c)` a tie-breaker of a `(p, q)`-adapted
resolution `(f; F_•; a_•; p_•; r_•)` with test boundary `A'`, and `ι : F_{j₀} ⟶ Y` the closed
immersion. Let `H'`, `B''` be the pull-backs of `H` and `⌊a(K_X + Δ)⌋` along `f`, and `H_F`,
`B_F` divisors on `F_{j₀}` with `𝒪(H_F) ≅ ι^* 𝒪_Y(H')` and `𝒪(B_F) ≅ ι^* 𝒪_Y(B'')`. Then for
integers `p', q'` with `(1 + c) p ≤ p'`, `(1 + c) q ≤ q'` and `aq' - rp' ≤ aq - rp`, and every
pull-back `B'` of `p'H + q'a(K_X + Δ)` along `f`, the Euler characteristic function of
`(F_{j₀}; H_F, B_F; A'|_{F_{j₀}})` at `(p', q')` is `dim_k H⁰(F_{j₀}, ι^* 𝒪_Y(B' + ⌈A'⌉))`. -/
@[mmp "lem_km3b_strip_restricted_euler_equals_h0"]
public theorem IsStripTieBreaker.eulerPolynomial_restrict_eq_finrank
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hpq : 0 < (a * q : ℝ) - r * p) {p' q' : ℤ}
    (hp' : (1 + c) * p ≤ p') (hq' : (1 + c) * q ≤ q')
    (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p)
    [IsLocallyNoetherian (F j₀).idealSheaf.subscheme] [IsNormal (F j₀).idealSheaf.subscheme]
    {hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {H' : Divisor Y} (hH' : H.IsPullback f hHf H')
    {hBf : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp}
    {B'' : Divisor Y} (hB'' : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsPullback f hBf B'')
    {HF BF : Divisor (F j₀).idealSheaf.subscheme}
    (eH : Nonempty (HF.divisorialSheaf ≅
      (Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj H'.divisorialSheaf))
    (eB : Nonempty (BF.divisorialSheaf ≅
      (Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj B''.divisorialSheaf))
    {hM : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hM B') :
    Divisor.eulerPolynomial k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) ![HF, BF]
        ((tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).restrictPrimeDivisor (F j₀))
        ![p', q'] =
      (Module.finrank k (cohomologyOverField k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)
        ((Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj
          (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
        0) : ℤ) := by
  classical
  set ι := (F j₀).idealSheaf.subschemeι
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  haveI : AlgebraicGeometry.IsVariety k sX := h.isKltPair.1.1.1
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans h.isKltPair.1.2.1.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdim
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  haveI : IsSmoothVariety k (f ≫ sX) := {}
  haveI : IsProper f := h.isLogResolution.isProper
  have hsmF := isSmoothScheme_subschemeι_comp h.toIsStripAdaptedResolution j₀
  haveI : IsIntegral (F j₀).idealSheaf.subscheme := (F j₀).integral
  haveI : Smooth (ι ≫ f ≫ sX) := (isSmoothScheme_iff _).mp hsmF
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ f ≫ sX) := ⟨⟩
  haveI : IsSmoothVariety k (ι ≫ f ≫ sX) := {}
  haveI : CompactSpace (F j₀).idealSheaf.subscheme := QuasiCompact.compactSpace_of_compactSpace ι
  haveI : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ f ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp hPY.isProjective)
  obtain ⟨m, rfl, hdimF⟩ := exists_topologicalKrullDim_subscheme_eq (f ≫ sX) hdim (F j₀)
  obtain ⟨KF, hKF⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ f ≫ sX) hsmF hdimF
  obtain ⟨hcY, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sX)
  obtain ⟨hcF, -, -, -, hinvF, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (ι ≫ f ≫ sX)
  have hres : ∀ D : Divisor Y, D.coeff (F j₀) = 0 →
      Restricts (F j₀) D (D.restrictPrimeDivisor (F j₀)) := fun D hD =>
    (Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k (f ≫ sX) (F j₀) D hD).2.1
  have h0 : Restricts (F j₀) 0 0 := by simpa [restrictPrimeDivisor_zero] using hres 0 (by simp)
  have hPF : Restricts (F j₀) B' (p' • HF + q' • BF) := by
    rw [eq_add_of_isPullback_stripDivisor h.toIsRationalityDatum hH' hB'' hB']
    exact (Restricts.zsmul hcY hcF hinvF h0 eH p').add hcY hcF
      (Restricts.zsmul hcY hcF hinvF h0 eB q')
  obtain ⟨hb, hpb⟩ := isPullback_toQDivisor_stripDivisor h.toIsRationalityDatum hB'
  have hNF := QDivisor.isAmple_add_restrictPrimeDivisor_sub_of_isAmple (f ≫ sX) hsm (F j₀) hsmF
    hKY hKF (hcY B') (coeff_tieBreakerBoundary_self h.injective _ aj pj j₀ c)
    (IsStripTieBreaker.isAmple_of_isStripTestDivisor h hr hpq hp' hq' hpq'
      ⟨hKY, hb, _, hpb, by rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]⟩)
    (hcF _) hPF
  have hvan := finrank_cohomologyOverField_add_roundUp_eq_zero (ι ≫ f ≫ sX) hsmF hKF _
    (isSNC_restrictPrimeDivisor_tieBreakerBoundary h.toIsStripAdaptedResolution _ j₀ c) hNF
  refine eulerPolynomial_pair_eq_finrank _ _ _ _ _ _ (Classical.choice ?_) hvan
  rw [roundUp_restrictPrimeDivisor_tieBreakerBoundary hsm h.toIsStripAdaptedResolution _ j₀ c
    hsmF (hcY 0)]
  exact hPF.add hcY hcF (hres _ (by
    rw [DivisorWithCoeffs.coeff_roundUp, coeff_tieBreakerBoundary_self h.injective,
      Int.ceil_zero]))

end MMP.Mori

end
