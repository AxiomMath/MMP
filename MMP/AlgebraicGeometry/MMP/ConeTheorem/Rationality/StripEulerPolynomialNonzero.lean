module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripTestDivisorAmple
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.EulerPolynomialNonvanishing
public import MMP.AlgebraicGeometry.Positivity.AmpleAdjunctionRestriction

@[expose] public section

section

/-!
## Proof of Kollár–Mori 3.4 Step 9

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r > 0`, `(j₀, c)` a tie-breaker of a
`(p, q)`-adapted resolution `f : Y ⟶ X` with test boundary `A'`, and `F = F_{j₀}` with closed
immersion `ι : F ⟶ Y`. Let `H_F`, `B_F` be divisors on `F` with `𝒪_F(H_F) ≅ ι^* 𝒪_Y(f^*H)` and
`𝒪_F(B_F) ≅ ι^* 𝒪_Y(f^*⌊a(K_X + Δ)⌋)`.

`F` is a smooth projective variety, the restriction `A'|_F` has snc support, and its round-up is
effective: every nonzero coefficient of `A'|_F` is a coefficient `-c r_j + a_j - p_j > -1` of
`A'`. Choose integers `u₂ ≥ max(0, (1 + c) q)` and `u₁ ≥ (1 + c) p` with `a u₂ ≤ r u₁`. Then the
test divisor `N(u₁, u₂)` is ample, so the adjoint restriction `u₁ H_F + u₂ B_F + A'|_F - K_F` is
ample on `F`, and `u₁ H + u₂ a (K_X + Δ)` is nef, hence so are its pull-back to `Y` and the
restriction `u₁ H_F + u₂ B_F` of that pull-back to `F`. The non-vanishing of the Euler
characteristic function along a nef ray then gives `Q(m u₁, m u₂) ≠ 0` for `m ≫ 0`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4 Step 9
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bStripRestrictedPolynomialNonzeroProof

section Nef

variable {k : Type} [Field k]

/-- If `u ≫ s_W = s_V` and the curve `C ⊆ V` is not contracted by `u`, its image `u(C)` is a
proper curve in `W`. -/
private theorem isCurve_imageι_of_comp_eq {V W C : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sW] {u : V ⟶ W} (hu : u ≫ sW = sV)
    (i : C ⟶ V) [AlgebraicGeometry.IsCurve k (i ≫ sV)] [IsProper (i ≫ sV)]
    (hpt : ¬ ∃ w : W, Set.range (i ≫ u) = {w}) :
    IsProper ((i ≫ u).imageι ≫ sW) ∧ AlgebraicGeometry.IsCurve k ((i ≫ u).imageι ≫ sW) := by
  have e : (i ≫ u) ≫ sW = i ≫ sV := by rw [Category.assoc, hu]
  have : IsProper ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : AlgebraicGeometry.IsCurve k ((i ≫ u) ≫ sW) := e ▸ inferInstance
  have : IsProper (i ≫ u) := IsProper.of_comp (i ≫ u) sW
  exact ⟨isProper_imageι_comp (i ≫ u) sW, isCurve_imageι_comp sW (i ≫ u) hpt⟩

/-- **The pull-back of a nef `ℚ`-divisor is nef.** For a morphism `u : V ⟶ W` of normal varieties
over `k` and a curve `C ⊆ V`, `(u^*L · C)` is `0` if `u(C)` is a point and a nonnegative multiple
of `(L · u(C))` otherwise. -/
private theorem isNef_of_isPullback {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sV]
    [AlgebraicGeometry.IsVariety k sW] [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian W] [IsNormal W] {u : V ⟶ W} (hu : u ≫ sW = sV) {L : QDivisor W}
    (hL : L.IsNef k sW)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') : L'.IsNef k sV := by
  refine ⟨h.isQCartier hL.1, fun C i _ _ _ hC => ?_⟩
  have : AlgebraicGeometry.IsCurve k (i ≫ sV) := { topologicalKrullDim_eq_one := hC }
  by_cases hpt : ∃ w : W, Set.range (i ≫ u) = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu i hL.1 h hpt).ge
  · obtain ⟨_, hcurve⟩ := isCurve_imageι_of_comp_eq hu i hpt
    rw [intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu i hL.1 h hcurve]
    exact mul_nonneg (by positivity)
      (hL.2 _ (i ≫ u).imageι hcurve.topologicalKrullDim_eq_one)

/-- If `H + tK` is nef in the sense of `QDivisor.IsNefCombination` for a rational `t`, then the
`ℚ`-divisor `H + tK` is nef. -/
private theorem isNef_add_smul_of_isNefCombination {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {H K : QDivisor X} {t : ℚ}
    (h : QDivisor.IsNefCombination k sX H K t) : (H + t • K).IsNef k sX := by
  obtain ⟨hH, hK, hC⟩ := h
  have htK : (t • K).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hK t
  have hq : (H + t • K).IsQCartier := hH.add htK
  refine ⟨hq, fun C i _ _ _ hC' => ?_⟩
  have := hC C i hC'
  rw [QDivisor.intersectionNumber_add' k sX i hC'.le H (t • K) hH htK hq,
    MMP.Fourfold.intersectionNumber_smul sX i hC'.le K hK t htK]
  exact_mod_cast this

/-- **Nefness restricts to closed subschemes.** If `D` is a nef Cartier divisor on `Y`,
`ι : Z ⟶ Y` a closed immersion and `E` a Cartier divisor on `Z` with `𝒪_Z(E) ≅ ι^* 𝒪_Y(D)`, then
`E` is nef. -/
private theorem isNef_of_iso_pullback {Y Z : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY] [IsLocallyNoetherian Z] [IsNormal Z]
    (ι : Z ⟶ Y) [IsClosedImmersion ι] {D : Divisor Y} (hD : D.IsNef k sY)
    {E : Divisor Z} (hE : E.IsCartier)
    (e : E.divisorialSheaf ≅ (Scheme.Modules.pullback ι).obj D.divisorialSheaf) :
    E.IsNef k (ι ≫ sY) := by
  obtain ⟨hDc, hDn⟩ := hD
  refine ⟨hE, fun C i _ _ _ hC => ?_⟩
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := QuasiCompact.compactSpace_of_compactSpace (ι ≫ sY)
  haveI := hDc.isInvertibleModule_divisorialSheaf
  haveI := hE.isInvertibleModule_divisorialSheaf
  haveI := MMP.Mori.isInvertible_pullback_obj ι D.divisorialSheaf
  haveI : IsProper ((i ≫ ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h1 : E.degreeOn k (ι ≫ sY) i hC.le hE = D.degreeOn k sY (i ≫ ι) hC.le hDc := by
    change MMP.Mori.degreeOn k (ι ≫ sY) i hC.le E.divisorialSheaf =
      MMP.Mori.degreeOn k sY (i ≫ ι) hC.le D.divisorialSheaf
    rw [degreeOn_eq_of_iso k (ι ≫ sY) i hC.le e]
    exact degreeOn_pullback_eq_degreeOn_comp (ι ≫ sY) sY ι i rfl hC.le _
  rw [h1]
  exact hDn C (i ≫ ι) hC

end Nef

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

/-- Cancellation: if `a + b ↝ X` and `a ↝ a'`, then `b ↝ X - a'`. -/
private theorem Restricts.cancel [IsIntegral F.idealSheaf.subscheme]
    (hY : ∀ D : Divisor Y, D.IsCartier) (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier)
    (hinv : ∀ L : F.idealSheaf.subscheme.Modules,
      Stacks.Ample.IsInvertibleModule F.idealSheaf.subscheme L →
        ∃ G : Divisor F.idealSheaf.subscheme, Nonempty (G.divisorialSheaf ≅ L))
    {a b : Divisor Y} {a' X : Divisor F.idealSheaf.subscheme}
    (h : Restricts F (a + b) X) (ha : Restricts F a a') : Restricts F b (X - a') := by
  haveI := (hY b).isInvertibleModule_divisorialSheaf
  obtain ⟨G, ⟨eG⟩⟩ := hinv ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj b.divisorialSheaf)
    inferInstance
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := Restricts.add hY hF ha ⟨eG⟩
  have hl : X.LinearlyEquivalent (a' + G) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ e'.symm)
  have hl' : (X - a').LinearlyEquivalent G := by
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
  · have h := Restricts.cancel hY hF hinv (b := -((m : ℤ) • a)) (X := 0)
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

/-- For a rationality datum `(X, Δ, a, H)` and a dominant `f : Y ⟶ X` with pull-backs
`H' = f^*H` and `B'' = f^*⌊a(K_X + Δ)⌋`, the divisor `u₁ H' + u₂ B''` is a pull-back of the
`ℚ`-divisor `u₁ H + u₂ a (K_X + Δ)`. -/
private theorem isPullback_toQDivisor_zsmul_add_zsmul {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H) {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] [IrreducibleSpace Y] {f : Y ⟶ X} [IsDominant f]
    {hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {H' : Divisor Y} (hH' : H.IsPullback f hHf H')
    {hBf : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (a • (Divisor.toQDivisor K + Δ)).roundDown.supp}
    {B'' : Divisor Y} (hB'' : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsPullback f hBf B'')
    (u₁ u₂ : ℤ) :
    ∃ hb, (u₁ • Divisor.toQDivisor H + (u₂ * a) • (Divisor.toQDivisor K + Δ)).IsPullback f hb
      (Divisor.toQDivisor (u₁ • H' + u₂ • B'')) := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hr0 : (a • (Divisor.toQDivisor K + Δ)).roundDown = D₀ := by
    rw [← hD₀, roundDown_toQDivisor]
  have hDc : (a • (Divisor.toQDivisor K + Δ)).roundDown.IsCartier := hr0 ▸ hD₀c
  have hM := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f
    (stripDivisor K Δ a H u₁ u₂)
  have hB' : (stripDivisor K Δ a H u₁ u₂).IsPullback f hM (u₁ • H' + u₂ • B'') :=
    Divisor.IsPullback.add (h.isCartier_H.zsmul u₁) (hDc.zsmul u₂) hM
      (hH'.zsmul h.isCartier_H u₁ fun Z hZ => hHf Z (supp_zsmul_le H u₁ hZ))
      (hB''.zsmul hDc u₂ fun Z hZ => hBf Z (supp_zsmul_le _ u₂ hZ))
  have hMQ : Divisor.toQDivisor (stripDivisor K Δ a H u₁ u₂) =
      u₁ • Divisor.toQDivisor H + (u₂ * a) • (Divisor.toQDivisor K + Δ) := by
    rw [stripDivisor, hr0, map_add, map_zsmul, map_zsmul, hD₀, smul_smul]
  rw [← hMQ]
  exact ⟨_, QDivisor.isPullback_toQDivisor ((h.isCartier_H.zsmul u₁).add (hDc.zsmul u₂))
    (fun Z hZ => hM Z (by rwa [Divisor.supp_toQDivisor] at hZ)) hB'⟩

/-- A divisor supported on the components `F_j` of an adapted resolution is snc. -/
private theorem isSNC_of_forall_exists_eq {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) {R : Type*} [CommRing R]
    (D : DivisorWithCoeffs R Y) (hD : ∀ E, D.coeff E ≠ 0 → ∃ j, F j = E) :
    D.IsSNC (f ≫ sX) := by
  classical
  refine h.isSNC.of_support_subset fun E hE => ?_
  obtain ⟨j, rfl⟩ := hD E (Finsupp.mem_support_iff.mp hE)
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finset.sum_eq_single j
    (fun b _ hb => Finsupp.single_eq_of_ne' (h.injective.ne hb)) (by simp)]
  simp

/-- Every component with nonzero coefficient in the test boundary `A'` is some `F_j` with
`j ≠ j₀`. -/
private theorem exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero {Y : Scheme.{0}} {s : ℕ}
    {F : Fin s → MMP.Mori.PrimeDivisor Y} {r aj pj : Fin s → ℚ} {j₀ : Fin s} {c : ℚ}
    {E : MMP.Mori.PrimeDivisor Y}
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
  obtain ⟨j, hj, hjE⟩ := exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero hne
  exact hj (hF hjE)

/-- A dimension `d ≠ ⊥` with `d + 1 = n` is `n - 1`, and `n ≥ 1`. -/
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

/-- The coefficients of the restriction of `∑_{j ∈ s} γ_j F_j` to a prime divisor `F_{j'}`
(`j' ∉ s`, the `F_j` distinct) are `∑_{j ∈ s} (F_j · Q) γ_j`. -/
private theorem coeff_restrictPrimeDivisor_sum_single {Y : Scheme.{0}} {ι : Type*}
    [DecidableEq ι] [IsLocallyNoetherian Y] [CompactSpace Y]
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

/-- The coefficient of the test boundary `A' = ∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j` along
`F_j`, `j ≠ j₀`. -/
private theorem coeff_tieBreakerBoundary_of_ne {Y : Scheme.{0}} {s : ℕ}
    {F : Fin s → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F) (r aj pj : Fin s → ℚ)
    (j₀ : Fin s) (c : ℚ) {j : Fin s} (hj : j ≠ j₀) :
    (tieBreakerBoundary F r aj pj j₀ c).coeff (F j) = -c * r j + aj j - pj j := by
  classical
  rw [tieBreakerBoundary, DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply,
    Finset.sum_eq_single j (fun b _ hb => Finsupp.single_eq_of_ne' (hF.ne hb))
      (fun h' => absurd (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩) h')]
  simp

/-- The lattice point of the strip: `u₂ = max(0, ⌈(1 + c) q⌉)` and
`u₁ = max(⌈(1 + c) p⌉, ⌈a u₂ / r⌉)` satisfy `u₁ ≥ (1 + c) p > 0`, `u₂ ≥ max(0, (1 + c) q)` and
`a u₂ ≤ r u₁`. -/
private theorem exists_strip_point {a p q : ℤ} {c : ℚ} {r : ℝ} (hr : 0 < r) (hc : 0 < 1 + c)
    (hp : 0 < p) :
    ∃ u₁ u₂ : ℤ, (1 + c) * p ≤ u₁ ∧ (1 + c) * q ≤ u₂ ∧ 0 ≤ u₂ ∧ (0 : ℚ) < u₁ ∧
      ((u₂ * a : ℤ) : ℝ) ≤ r * u₁ := by
  set u₂ : ℤ := max 0 ⌈(1 + c) * q⌉
  have h₁ : (1 + c) * p ≤ (max ⌈(1 + c) * p⌉ ⌈((u₂ * a : ℤ) : ℝ) / r⌉ : ℤ) :=
    (Int.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
  refine ⟨_, u₂, h₁, (Int.le_ceil _).trans (by exact_mod_cast le_max_right _ _),
    le_max_left _ _, (mul_pos hc (by exact_mod_cast hp)).trans_le h₁, ?_⟩
  rw [← div_le_iff₀' hr]
  exact (Int.le_ceil _).trans (by exact_mod_cast le_max_right _ _)

/-- **The restricted test boundary is snc.** For a `(p, q)`-adapted resolution, the restriction
of `A' = ∑_{j ≠ j₀} γ_j F_j` to `F_{j₀}` is snc on `F_{j₀}`: its support lies in that of the
reduced snc divisor `(∑_{j ≠ j₀} F_j)|_{F_{j₀}}`. -/
private theorem isSNC_restrictPrimeDivisor_tieBreakerBoundary {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj)
    [AlgebraicGeometry.IsVariety k (f ≫ sX)] [Smooth (f ≫ sX)]
    (r : Fin s → ℚ) (j₀ : Fin s) (c : ℚ) :
    ((tieBreakerBoundary F r aj pj j₀ c).restrictPrimeDivisor (F j₀)).IsSNC
      ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) := by
  classical
  set S := Finset.univ.erase j₀
  have hj₀ : j₀ ∉ S := Finset.notMem_erase j₀ _
  have hFD : F j₀ ∉ S.image F := fun hm => by
    obtain ⟨j, hj, hjF⟩ := Finset.mem_image.mp hm
    exact hj₀ (h.injective hjF ▸ hj)
  have hsnc : DivisorWithCoeffs.IsSNC (f ≫ sX)
      (Finsupp.single (F j₀) (1 : ℤ) + ∑ E ∈ S.image F, Finsupp.single E (1 : ℤ)) := by
    refine isSNC_of_forall_exists_eq h _ fun E hE => ?_
    by_cases hE0 : F j₀ = E
    · exact ⟨j₀, hE0⟩
    · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff, DivisorWithCoeffs.coeff,
        Finsupp.single_eq_of_ne' hE0, zero_add, Finsupp.finset_sum_apply] at hE
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
  have hl : (F j).intersectionLength (F j₀).idealSheaf.subschemeι Q ≠ 0 :=
    fun h0 => hne (by rw [h0, zero_smul])
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨j, hj, Nat.pos_of_ne_zero hl⟩).ne'

/-- The round-up of the test boundary of a tie-breaker is effective. -/
private theorem isEffective_roundUp_tieBreakerBoundary {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ} {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) :
    (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp.IsEffective := by
  intro E
  rw [DivisorWithCoeffs.coeff_roundUp]
  by_cases hE : (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).coeff E = 0
  · rw [hE, Int.ceil_zero]
  obtain ⟨j, hj, rfl⟩ := exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero hE
  rw [coeff_tieBreakerBoundary_of_ne h.injective _ aj pj j₀ c hj]
  have hlt : ((-1 : ℤ) : ℚ) < -c * (rj j : ℚ) + aj j - pj j := by
    rcases Nat.eq_zero_or_pos (rj j) with h0j | hpos
    · rw [h0j]
      push_cast
      linarith [h.lt_one_add j]
    · have h1 := h.lt_div j hj hpos
      rw [lt_div_iff₀ (by exact_mod_cast hpos)] at h1
      push_cast
      linarith
  have := Int.lt_ceil.mpr hlt
  omega

/-- **The restricted test boundary has effective round-up.** The round-up of the restriction
`A'|_{F_{j₀}}` of the test boundary is effective. -/
private theorem isEffective_roundUp_restrictPrimeDivisor_tieBreakerBoundary {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ} {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c)
    [AlgebraicGeometry.IsVariety k (f ≫ sX)] (hsm : IsSmoothScheme (f ≫ sX))
    (hsmF : IsSmoothScheme ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX)) :
    ((tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).restrictPrimeDivisor
      (F j₀)).roundUp.IsEffective := by
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c
  have hAF : A.coeff (F j₀) = 0 := coeff_tieBreakerBoundary_self h.injective _ aj pj j₀ c
  have hsnc : DivisorWithCoeffs.IsSNC (f ≫ sX) (Finsupp.single (F j₀) (1 : ℚ) + A) := by
    refine isSNC_of_forall_exists_eq h.toIsStripAdaptedResolution _ fun E hE => ?_
    by_cases hE0 : F j₀ = E
    · exact ⟨j₀, hE0⟩
    · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff,
        Finsupp.single_eq_of_ne' hE0, zero_add] at hE
      obtain ⟨j, -, hj⟩ := exists_ne_and_eq_of_coeff_tieBreakerBoundary_ne_zero hE
      exact ⟨j, hj⟩
  have hLF : ¬ ((F j₀).support : Set Y) ⊆ ((0 : Divisor Y).supp : Set Y) := by
    rw [DivisorWithCoeffs.supp_zero]
    intro hsub
    exact hsub (a := (F j₀).genericPoint) (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
  have hround := DivisorWithCoeffs.restrictPrimeDivisor_roundUp (f ≫ sX) (R := ℚ) inferInstance
    hsm (F j₀) hsmF 0 Divisor.isCartier_zero hLF A hAF hsnc
  rw [map_zero, zero_add] at hround
  rw [← hround]
  intro Q
  haveI : IsNoetherian Y := ⟨⟩
  have hAuF : A.roundUp.coeff (F j₀) = 0 := by
    rw [DivisorWithCoeffs.coeff_roundUp, hAF, Int.ceil_zero]
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ _ hAuF]
  exact Finsupp.sum_nonneg fun E _ => nsmul_nonneg (isEffective_roundUp_tieBreakerBoundary h E) _

end MMP.FourfoldProofs.Km3bStripRestrictedPolynomialNonzeroProof

end

section

/-!
# The restricted Euler characteristic function of the strip is not identically zero

Let `(X, Δ, a, H)` be a rationality datum with positive nef threshold `r` of `H` with respect
to `K_X + Δ`, let `p, q > 0` be integers with `aq - rp > 0`, let `(j₀, c)` be a tie-breaker of a
`(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` with test boundary
`A' = ∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j`, and put `F = F_{j₀}`. Then the Euler characteristic
function `Q` of `(F; f^*H|_F, f^*(a(K_X + Δ))|_F; A'|_F)` is not identically zero.
Indeed, for integers `u₁ ≥ (1 + c) p`, `u₂ ≥ max(0, (1 + c) q)` with `a u₂ ≤ r u₁` (possible as
`r > 0`), the divisor `(f^*(u₁H + u₂a(K_X + Δ)) + A')|_F - K_F` is numerically equivalent to the
ample `N(u₁, u₂)|_F` and `u₁H + u₂a(K_X + Δ)` is nef, so `Q(m u₁, m u₂) ≠ 0` for `m ≫ 0`.

## Main results

* `MMP.Mori.IsStripTieBreaker.eulerPolynomial_restrict_ne_zero`: the statement above.

## Implementation notes

The prime divisor `F = F_{j₀}` is the integral closed subscheme `(F j₀).idealSheaf.subscheme`
with inclusion `ι = (F j₀).idealSheaf.subschemeι`, a scheme over `k` through `ι ≫ f ≫ sX`.
Since `F` may be a component of the pull-backs of `H` and of `a(K_X + Δ)`, the restrictions
`f^*H|_F` and `f^*(a(K_X + Δ))|_F` are taken as line bundles: they are any divisors `H_F` and
`B_F` on `F` with `𝒪_F(H_F) ≅ ι^* 𝒪_Y(f^*H)` and `𝒪_F(B_F) ≅ ι^* 𝒪_Y(f^*⌊a(K_X + Δ)⌋)`, and the
statement holds for every such choice. The test boundary has coefficient `0` along `F`, so
`A'|_F` is the divisor restriction `MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`. "Not
identically zero" is `≠ 0` in the function space `(Fin 2 → ℤ) → ℤ`. The ground field is
algebraically closed of characteristic zero, as Kawamata–Viehweg vanishing requires.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bStripRestrictedPolynomialNonzeroProof in
/-- **The restricted Euler characteristic function is not identically zero**
(Kollár–Mori 3.4, Step 9). Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r > 0`
of `H` with respect to `K_X + Δ`, `p, q > 0` integers with `0 < aq - rp`, `(j₀, c)` a
tie-breaker of a `(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` with test boundary `A'`,
and `ι : F_{j₀} ⟶ Y` the closed immersion. Let `H'`, `B''` be the pull-backs of `H` and
`⌊a(K_X + Δ)⌋` along `f`, and `H_F`, `B_F` divisors on `F_{j₀}` with `𝒪(H_F) ≅ ι^* 𝒪_Y(H')` and
`𝒪(B_F) ≅ ι^* 𝒪_Y(B'')`. Then the Euler characteristic function of
`(F_{j₀}; H_F, B_F; A'|_{F_{j₀}})` is not identically zero. -/
@[mmp "lem_km3b_strip_restricted_polynomial_nonzero"]
public theorem IsStripTieBreaker.eulerPolynomial_restrict_ne_zero
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r) (hpq : 0 < (a * q : ℝ) - r * p)
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
      (Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj B''.divisorialSheaf)) :
    Divisor.eulerPolynomial k ((F j₀).idealSheaf.subschemeι ≫ f ≫ sX) ![HF, BF]
        ((tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).restrictPrimeDivisor (F j₀)) ≠
      0 := by
  set ι := (F j₀).idealSheaf.subschemeι
  -- `Y` is a smooth projective variety of dimension `n`
  haveI hPY : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have hKX : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  haveI : AlgebraicGeometry.IsVariety k sX := h.isKltPair.1.1.1
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans hKX.1
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdim
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hPY.toIsVariety
  haveI : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hsm
  haveI : IsSmoothVariety k (f ≫ sX) := { toSmooth := inferInstance }
  haveI : IsProper f := h.isLogResolution.isProper
  haveI : IsDominant f := h.isLogResolution.isBirationalMorphism.isDominant
  -- `F` is a smooth projective variety of dimension `n - 1`
  have hsmF : IsSmoothScheme (ι ≫ f ≫ sX) := h.isSNC.1 (F j₀) (by
    classical
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, h.injective.eq_iff])
  haveI : IsIntegral (F j₀).idealSheaf.subscheme := (F j₀).integral
  haveI : Smooth (ι ≫ f ≫ sX) := (isSmoothScheme_iff _).mp hsmF
  haveI : IsSmoothVariety k (ι ≫ f ≫ sX) := { toIsVariety := ⟨⟩, toSmooth := inferInstance }
  haveI : CompactSpace (F j₀).idealSheaf.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace ι
  haveI : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ f ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism k _).mpr
      ((MMP.isProjectiveMorphism_of_isClosedImmersion ι).comp hPY.isProjective)
  obtain ⟨m, rfl, hdimF⟩ : ∃ m : ℕ, n = m + 1 ∧
      topologicalKrullDim (F j₀).idealSheaf.subscheme = m := by
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX)
      (F j₀).genericPoint
    rw [(F j₀).coheight_genericPoint, hdim,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← MMP.Mori.topologicalKrullDim_subscheme_eq] at h1
    refine exists_eq_add_one_of_add_one_eq ?_ (by exact_mod_cast h1)
    rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    infer_instance
  obtain ⟨KF, hKF⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (ι ≫ f ≫ sX) hsmF hdimF
  obtain ⟨hcY, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sX)
  obtain ⟨hcF, -, -, -, hinvF, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (ι ≫ f ≫ sX)
  have h0 : Restricts (F j₀) 0 0 := by
    have := (Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k (f ≫ sX) (F j₀) 0
      (by simp)).2.1
    have h00 := DivisorWithCoeffs.restrictPrimeDivisor_zsmul (0 : Divisor Y) (F j₀) (by simp) 0
    rw [zero_smul, zero_smul] at h00
    rwa [h00] at this
  -- the lattice point `(u₁, u₂)` and the pull-back `B' = u₁ H' + u₂ B''`
  have hc : 0 < 1 + c := by
    have : (0 : ℚ) < rj j₀ := by exact_mod_cast h.pos_r
    have : 0 < c := h.eq_div ▸ div_pos (by linarith [h.lt_one_add j₀]) this
    linarith
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₂0, hu₁0, htr⟩ := exists_strip_point (a := a) (q := q) hr0 hc h.pos_p
  obtain ⟨hb, hpb⟩ := isPullback_toQDivisor_zsmul_add_zsmul h.toIsRationalityDatum hH' hB'' u₁ u₂
  set B' : Divisor Y := u₁ • H' + u₂ • B''
  -- `𝒪_F(u₁ H_F + u₂ B_F) ≅ ι^* 𝒪_Y(B')`
  have hPF : Restricts (F j₀) B' (u₁ • HF + u₂ • BF) :=
    (Restricts.zsmul hcY hcF hinvF h0 eH u₁).add hcY hcF (Restricts.zsmul hcY hcF hinvF h0 eB u₂)
  have hsum : ∑ i, ![u₁, u₂] i • ![HF, BF] i = u₁ • HF + u₂ • BF := by simp [Fin.sum_univ_two]
  -- `N(u₁, u₂) = B' + A' - F - K_Y` is ample, so `u₁ H_F + u₂ B_F + A'|_F - K_F` is ample
  have hN : IsStripTestDivisor sX (m + 1) K Δ a H f KY F aj pj rj j₀ c u₁ u₂
      (Divisor.toQDivisor B' + tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c -
        Divisor.toQDivisor (Finsupp.single (F j₀) 1) - Divisor.toQDivisor KY) :=
    ⟨hKY, hb, _, hpb, by rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]⟩
  have hNamp := h.isAmple_of_isStripTestDivisor hr hpq hu₁ hu₂
    (by push_cast at htr; linarith) hN
  have hNF := QDivisor.isAmple_add_restrictPrimeDivisor_sub_of_isAmple (f ≫ sX) hsm (F j₀) hsmF
    hKY hKF (hcY B') (coeff_tieBreakerBoundary_self h.injective _ aj pj j₀ c) hNamp (hcF _) hPF
  -- `u₁ H + u₂ a (K_X + Δ)` is nef, hence so are its pull-back `B'` and the restriction to `F`
  have hWX := isNef_add_smul_of_isNefCombination
    (MMP.Positivity.IsRationalityDatum.isNefCombination_of_le h.toIsRationalityDatum hr hu₁0
      (t := (((u₂ * a : ℤ) : ℚ) : ℝ)) (by exact_mod_cast mul_nonneg hu₂0 h.pos.le)
      (by exact_mod_cast htr))
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul] at hWX
  have hPFnef := isNef_of_iso_pullback ι ((QDivisor.isNef_toQDivisor_iff B' (hcY B')).mp
    (isNef_of_isPullback rfl hWX hpb)) (hcF _) hPF.some
  -- non-vanishing along the nef ray `m (u₁, u₂)`
  intro h0
  obtain ⟨_, hm⟩ := (Divisor.eventually_eulerPolynomial_zsmul_ne_zero (ι ≫ f ≫ sX) hsmF hKF
    ![HF, BF] _
    (isSNC_restrictPrimeDivisor_tieBreakerBoundary h.toIsStripAdaptedResolution _ j₀ c)
    (isEffective_roundUp_restrictPrimeDivisor_tieBreakerBoundary h hsm hsmF) ![u₁, u₂]
    (hsum ▸ hPFnef) (hsum ▸ hNF)).exists
  exact hm (by rw [h0]; rfl)

end MMP.Mori

end
