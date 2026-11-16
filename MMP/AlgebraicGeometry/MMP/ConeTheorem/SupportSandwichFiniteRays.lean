module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.AmplePerturbationFiniteRays
public import MMP.AlgebraicGeometry.Singularities.KltRelativeBigCore
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation

/-!
# Finitely many negative rays under a support sandwich

Let `h : Y ⟶ Z` be a projective birational morphism of normal projective varieties over an
algebraically closed field of characteristic zero, with `Y` `ℚ`-factorial, let `(Y, B)` be a dlt
pair with `B` a `ℚ`-divisor, and let `H ≥ 0` be a Cartier divisor on `Z` whose pull-back satisfies
`Supp ⌊B⌋ ⊆ Supp h^*H ⊆ Supp B`. Then only finitely many extremal rays of `NE̅(Y/Z)` are
`(K_Y + B)`-negative, each is spanned by the class of a rational curve contracted by `h`, and
`NE̅(Y/Z) = NE̅(Y/Z)_{(K_Y + B) ≥ 0} + ∑ R`, the sum over these rays.

## Main results

* `MMP.Fourfold.exists_finite_isExtremalRay_of_support_roundDown_subset_pullback`: the statement
  above.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero (`MMP.Mori.IsProjectiveSetting`).
* `H` is a Weil divisor on `Z` that is Cartier and effective, and `h^*H` is
  `MMP.Mori.Divisor.pullback`, defined when no generic point of `Y` maps into `Supp H` (for
  birational `h` this says `H` does not pass through the generic point of `Z`); it needs `Z`
  locally Noetherian and normal as instances, which `MMP.Mori.IsNormalVariety` already gives.
  Supports are compared as reduced divisors, `MMP.Mori.Divisor.supp` and
  `MMP.Mori.QDivisor.supp`.
* The degree of `K_Y + B` on `u ∈ N₁(Y/Z)` is `MMP.Fourfold.QDivisor.curveForm` evaluated at the
  image of `u` under the natural map `MMP.Mori.relativeToAbsolute`. The sum of the rays is their
  `PointedCone.hull` (finite nonnegative combinations), added pointwise to the nonnegative part.
* Proof: for small `δ > 0` the pair `(Y, B - δ h^*H)` is klt and has the same relative adjoint
  degrees as `(Y, B)`. Since `0` is `h`-big, the relative big-core translation writes
  `B - δ h^*H + T_Y = A' + C` with `A'` ample, `C` klt and `T_Y` numerically trivial over `Z`; the
  absolute cone theorem for `(Y, C)` and `A'` then gives a finite decomposition of `NE̅(Y)`, which
  descends to `NE̅(Y/Z)` because `NE̅(Z)` contains no line.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.7 and 3.25
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Pointwise

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.FourfoldProofs.FourfoldProjectiveSupportSandwichFiniteRaysProof

open MMP.Mori MMP.Fourfold

/-! ### Cones -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The closed half-line `ℝ_{≥0} x` spanned by `x`. -/
private def ray (x : V) : Set V := {w | ∃ c : ℝ, 0 ≤ c ∧ c • x = w}

/-- A vector lies on the half-line it spans. -/
private theorem mem_ray_self (x : V) : x ∈ ray x := ⟨1, zero_le_one, one_smul ℝ x⟩

/-- A positive multiple spans the same half-line. -/
private theorem ray_smul {c : ℝ} (hc : 0 < c) (x : V) : ray (c • x) = ray x := by
  ext w
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, mul_nonneg hd hc.le, by rw [mul_smul]⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d / c, div_nonneg hd hc.le, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩

/-- A linear map carries the half-line spanned by `x` onto the half-line spanned by its image. -/
private theorem image_ray {W : Type*} [AddCommGroup W] [Module ℝ W] (ι : V →ₗ[ℝ] W) (x : V) :
    ι '' ray x = ray (ι x) := by
  ext w
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (map_smul ι c x).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c • x, ⟨c, hc, rfl⟩, map_smul ι c x⟩

/-- An extremal face of a convex cone contains every summand of a finite sum of elements of the
cone lying in the face. -/
private theorem IsExtremalFace.mem_of_sum_mem {N : PointedCone ℝ V} {F : Set V}
    (hF : IsExtremalFace ℝ (N : Set V) F) {α : Type*} (s : Finset α) (a : α → V)
    (ha : ∀ i ∈ s, a i ∈ N) (hs : ∑ i ∈ s, a i ∈ F) : ∀ i ∈ s, a i ∈ F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at hs
    have hsN : ∑ i ∈ s, a i ∈ N := N.sum_mem fun i hi => ha i (Finset.mem_insert_of_mem hi)
    obtain ⟨h1, h2⟩ := hF.2.2.2 _ (ha j (Finset.mem_insert_self j s)) _ hsN hs
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h1
    · exact ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) h2 i hi

/-- If `x + y = 0` in a pointed cone without lines, then `x = 0`. -/
private theorem eq_zero_of_add_eq_zero {K : PointedCone ℝ V} (hK : K.lineal = ⊥) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (h : x + y = 0) : x = 0 := by
  have : x ∈ K.lineal := PointedCone.mem_lineal.2 ⟨hx, by rwa [neg_eq_of_add_eq_zero_right h]⟩
  rwa [hK, Submodule.mem_bot] at this

/-- A vanishing finite sum of elements of a pointed cone without lines has vanishing summands. -/
private theorem eq_zero_of_sum_eq_zero {K : PointedCone ℝ V} (hK : K.lineal = ⊥) {α : Type*}
    (s : Finset α) (b : α → V) (hb : ∀ i ∈ s, b i ∈ K) (h0 : ∑ i ∈ s, b i = 0) :
    ∀ i ∈ s, b i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj] at h0
    have hsK : ∑ i ∈ s, b i ∈ K := K.sum_mem fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hj0 : b j = 0 := eq_zero_of_add_eq_zero hK (hb j (Finset.mem_insert_self j s)) hsK h0
    rw [hj0, zero_add] at h0
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hj0
    · exact ih (fun i hi => hb i (Finset.mem_insert_of_mem hi)) h0 i hi

/-- An element of the cone spanned by a finite set is a nonnegative combination of its elements. -/
private theorem exists_eq_sum_of_mem_hull {G : Finset V} {x : V}
    (hx : x ∈ PointedCone.hull ℝ (G : Set V)) :
    ∃ f : V → ℝ, (∀ y, 0 ≤ f y) ∧ ∑ y ∈ G, f y • y = x := by
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
  exact ⟨fun y => (f y : ℝ), fun y => (f y).2, hf⟩

/-- A nonzero vector of an extremal ray spans it. -/
private theorem IsExtremalRay.eq_ray_of_mem {N R : Set V} (hR : IsExtremalRay ℝ N R) {r : V}
    (hr : r ∈ R) (hr0 : r ≠ 0) : R = ray r := by
  obtain ⟨-, u, -, rfl⟩ := hR
  obtain ⟨c, hc, rfl⟩ := hr
  have hc0 : 0 < c := lt_of_le_of_ne hc fun h => hr0 (by rw [← h, zero_smul])
  exact (ray_smul hc0 u).symm

variable {W U : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]

/-- If an injective `ι` carries `K'` onto `K ∩ ι(V)`, then `ι r ∈ K` forces `r ∈ K'`. -/
private theorem mem_of_map_mem {ι : V →ₗ[ℝ] W} (hι : Function.Injective ι)
    {K' : PointedCone ℝ V} {K : PointedCone ℝ W}
    (himage : ι '' (K' : Set V) = (K : Set W) ∩ Set.range ι) {r : V} (hr : ι r ∈ K) :
    r ∈ K' := by
  obtain ⟨r', hr', he⟩ : ι r ∈ ι '' (K' : Set V) := himage ▸ ⟨hr, r, rfl⟩
  rwa [← hι he]

/-- If an injective `ι` carries `K'` onto `K ∩ ι(V)`, a nonzero `r ∈ K'` whose image spans an
extremal ray of `K` spans an extremal ray of `K'`. -/
private theorem isExtremalRay_ray_of_isExtremalRay_image (ι : V →ₗ[ℝ] W)
    (hι : Function.Injective ι) {K' : PointedCone ℝ V} {K : PointedCone ℝ W}
    (himage : ι '' (K' : Set V) = (K : Set W) ∩ Set.range ι) {r : V} (hr0 : r ≠ 0)
    (hrK : r ∈ K') (hext : IsExtremalRay ℝ (K : Set W) (ray (ι r))) :
    IsExtremalRay ℝ (K' : Set V) (ray r) := by
  have hιK : ∀ v ∈ K', ι v ∈ K := fun v hv => (himage.subset ⟨v, hv, rfl⟩).1
  refine ⟨⟨?_, ⟨⟨0, le_rfl, zero_smul ℝ r⟩, ?_⟩, ?_, ?_⟩, r, hr0, rfl⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact K'.smul_mem hc hrK
  · rintro _ ⟨c, hc, rfl⟩ d hd
    exact ⟨d * c, mul_nonneg hd.le hc, by rw [mul_smul]⟩
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ⟨c + d, add_nonneg hc hd, add_smul c d r⟩
  · rintro u hu v hv ⟨c, hc, hcuv⟩
    obtain ⟨⟨a, ha, hau⟩, ⟨d, hd, hdv⟩⟩ := hext.1.2.2.2 (ι u) (hιK u hu) (ι v) (hιK v hv)
      ⟨c, hc, by rw [← map_add, ← hcuv, map_smul]⟩
    exact ⟨⟨a, ha, hι (by rw [map_smul, hau])⟩, ⟨d, hd, hι (by rw [map_smul, hdv])⟩⟩

/-- With `ι` as above and `M = L ∘ ι`, every nonnegative multiple of `r` lies in the cone spanned
by the `M`-negative extremal rays of `K'` when `ι r` spans an `L`-negative extremal ray of `K`. -/
private theorem smul_mem_hull_of_isExtremalRay (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι)
    {K' : PointedCone ℝ V} {K : PointedCone ℝ W}
    (himage : ι '' (K' : Set V) = (K : Set W) ∩ Set.range ι) (L : W →ₗ[ℝ] ℝ) (M : V →ₗ[ℝ] ℝ)
    (hLM : ∀ v, L (ι v) = M v) {r : V} (hext : IsExtremalRay ℝ (K : Set W) (ray (ι r)))
    (hLr : L (ι r) < 0) {a : ℝ} (ha : 0 ≤ a) :
    a • r ∈ PointedCone.hull ℝ
      (⋃₀ {R : Set V | IsExtremalRay ℝ (K' : Set V) R ∧ ∀ u ∈ R, u ≠ 0 → M u < 0}) := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hLr
  refine (PointedCone.hull ℝ _).smul_mem ha (Submodule.subset_span ⟨ray r,
    ⟨isExtremalRay_ray_of_isExtremalRay_image ι hι himage hr0
      (mem_of_map_mem hι himage (hext.1.1 (mem_ray_self _))) hext, ?_⟩, mem_ray_self r⟩)
  rintro _ ⟨c, hc, rfl⟩ hu0
  have hc0 : 0 < c := lt_of_le_of_ne hc fun h => hu0 (by rw [← h, zero_smul])
  rw [map_smul, smul_eq_mul, ← hLM]
  exact mul_neg_of_pos_of_neg hc0 hLr

/-- If `π` maps `K` into a cone without lines and kills `y + ∑ x ∈ G, f x • x` with `y` and every
`f x • x` in `K`, then `π` kills each `x ∈ G` with `f x ≠ 0`. -/
private theorem map_eq_zero_of_map_add_sum_eq_zero (π : W →ₗ[ℝ] U) {K : PointedCone ℝ W}
    {KU : PointedCone ℝ U} (hKU : KU.lineal = ⊥) (hπK : ∀ x ∈ K, π x ∈ KU) {G : Finset W}
    {f : W → ℝ} {y : W} (hy : y ∈ K) (hterms : ∀ x ∈ G, f x • x ∈ K)
    (h0 : π (y + ∑ x ∈ G, f x • x) = 0) : ∀ x ∈ G, f x ≠ 0 → π x = 0 := by
  rw [map_add, map_sum] at h0
  have hy0 : π y = 0 := eq_zero_of_add_eq_zero hKU (hπK y hy)
    (by simpa only [map_sum] using hπK _ (K.sum_mem hterms)) h0
  rw [hy0, zero_add] at h0
  intro x hx hfx
  have := eq_zero_of_sum_eq_zero hKU G _ (fun x hx => hπK _ (hterms x hx)) h0 x hx
  rw [map_smul, smul_eq_zero] at this
  exact this.resolve_left hfx

/-- Under the hypotheses of `finite_negative_rays_of_decomposition`, every `M`-negative extremal
ray of `K'` is spanned by a preimage of an element of `G`. -/
private theorem exists_eq_ray_of_isExtremalRay_of_decomposition (ι : V →ₗ[ℝ] W)
    {K' : PointedCone ℝ V} {K : PointedCone ℝ W}
    (hext : ∀ R, IsExtremalRay ℝ (K' : Set V) R → IsExtremalRay ℝ (K : Set W) (ι '' R))
    (L : W →ₗ[ℝ] ℝ) (M : V →ₗ[ℝ] ℝ) (hLM : ∀ v, L (ι v) = M v) (G : Finset W)
    (hGext : ∀ x ∈ G, IsExtremalRay ℝ (K : Set W) (ray x))
    (hdec : (K : Set W) = ((K : Set W) ∩ {z | 0 ≤ L z}) + (PointedCone.hull ℝ (G : Set W) : Set W))
    (R : Set V) (hR : IsExtremalRay ℝ (K' : Set V) R) (hneg : ∀ u ∈ R, u ≠ 0 → M u < 0) :
    ∃ x ∈ G, ∃ r, ι r = x ∧ R = ray r := by
  obtain ⟨hface, v, hv0, hRv⟩ := hext R hR
  have hvR : v ∈ ι '' R := hRv ▸ mem_ray_self v
  have hvK : v ∈ (K : Set W) := hface.1 hvR
  rw [hdec] at hvK
  obtain ⟨y, ⟨hyK, hyL⟩, n, hn, hyn⟩ := hvK
  beta_reduce at hyn
  obtain ⟨f, hf0, rfl⟩ := exists_eq_sum_of_mem_hull hn
  have hterms : ∀ x ∈ G, f x • x ∈ K := fun x hx =>
    K.smul_mem (hf0 x) ((hGext x hx).1.1 (mem_ray_self x))
  obtain ⟨hyR, hsR⟩ := hface.2.2.2 y hyK _ (K.sum_mem hterms) (by rwa [hyn])
  have hy0 : y = 0 := by
    obtain ⟨u, hu, rfl⟩ := hyR
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    · exact absurd (hLM u ▸ hyL : (0 : ℝ) ≤ M u) (not_le.2 (hneg u hu hu0))
  rw [hy0, zero_add] at hyn
  obtain ⟨x, hxG, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hyn ▸ hv0 :
    ∑ x ∈ G, f x • x ≠ 0)
  have hfx : f x ≠ 0 := fun h => hx0 (by rw [h, zero_smul])
  have hxne : x ≠ 0 := fun h => hx0 (by rw [h, smul_zero])
  have hxR : x ∈ ι '' R := by
    have h1 := IsExtremalFace.mem_of_sum_mem hface G _ hterms hsR x hxG
    have h2 := hface.2.1.2 _ h1 (f x)⁻¹ (inv_pos.2 ((hf0 x).lt_of_ne' hfx))
    rwa [smul_smul, inv_mul_cancel₀ hfx, one_smul] at h2
  obtain ⟨r, hrR, rfl⟩ := hxR
  exact ⟨ι r, hxG, r, rfl,
    IsExtremalRay.eq_ray_of_mem hR hrR fun h => hxne (by rw [h, map_zero])⟩

/-- Under the hypotheses of `finite_negative_rays_of_decomposition`, `K'` lies in
`K'_{M ≥ 0} + ∑ R`, the sum over the `M`-negative extremal rays `R` of `K'`. -/
private theorem mem_add_hull_of_mem_of_decomposition (ι : V →ₗ[ℝ] W)
    (hι : Function.Injective ι) (π : W →ₗ[ℝ] U) {K' : PointedCone ℝ V} {K : PointedCone ℝ W}
    {KU : PointedCone ℝ U} (hKU : KU.lineal = ⊥) (hπK : ∀ x ∈ K, π x ∈ KU)
    (hπι : ∀ v, π (ι v) = 0) (himage : ι '' (K' : Set V) = (K : Set W) ∩ Set.range ι)
    (L : W →ₗ[ℝ] ℝ) (M : V →ₗ[ℝ] ℝ) (hLM : ∀ v, L (ι v) = M v) (G : Finset W)
    (hGext : ∀ x ∈ G, IsExtremalRay ℝ (K : Set W) (ray x))
    (hdec : (K : Set W) = ((K : Set W) ∩ {z | 0 ≤ L z}) + (PointedCone.hull ℝ (G : Set W) : Set W))
    (hlift : ∀ x ∈ G, π x = 0 → x ∈ Set.range ι) {z : V} (hz : z ∈ (K' : Set V)) :
    z ∈ ((K' : Set V) ∩ {z | 0 ≤ M z}) +
      (PointedCone.hull ℝ
        (⋃₀ {R : Set V | IsExtremalRay ℝ (K' : Set V) R ∧ ∀ u ∈ R, u ≠ 0 → M u < 0}) :
          Set V) := by
  classical
  have hιz : ι z ∈ (K : Set W) := (himage.subset ⟨z, hz, rfl⟩).1
  rw [hdec] at hιz
  obtain ⟨y, ⟨hyK, hyL⟩, n, hn, hyn⟩ := hιz
  beta_reduce at hyn
  obtain ⟨f, hf0, rfl⟩ := exists_eq_sum_of_mem_hull hn
  have hterms : ∀ x ∈ G, f x • x ∈ K := fun x hx =>
    K.smul_mem (hf0 x) ((hGext x hx).1.1 (mem_ray_self x))
  have hπx := map_eq_zero_of_map_add_sum_eq_zero π hKU hπK hyK hterms (by rw [hyn, hπι])
  have hρ : ∀ x ∈ G, f x ≠ 0 → ι (Function.invFun ι x) = x := fun x hx hfx =>
    Function.invFun_eq (hlift x hx (hπx x hx hfx))
  set Gn := G.filter fun x => L x < 0
  set Gp := G.filter fun x => ¬ L x < 0
  set b : V := ∑ x ∈ Gn, f x • Function.invFun ι x
  have hιb : ι b = ∑ x ∈ Gn, f x • x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [map_smul]
    by_cases hfx : f x = 0
    · rw [hfx, zero_smul, zero_smul]
    · rw [hρ x (Finset.mem_filter.1 hx).1 hfx]
  have hsplit : ∑ x ∈ Gn, f x • x + ∑ x ∈ Gp, f x • x = ∑ x ∈ G, f x • x :=
    Finset.sum_filter_add_sum_filter_not G (fun x => L x < 0) (fun x => f x • x)
  have hιa : ι (z - b) = y + ∑ x ∈ Gp, f x • x := by
    rw [map_sub, hιb, ← hyn, ← hsplit]
    abel
  refine ⟨z - b, ⟨mem_of_map_mem hι himage ?_, ?_⟩, b, ?_, sub_add_cancel z b⟩
  · rw [hιa]
    exact K.add_mem hyK (K.sum_mem fun x hx => hterms x (Finset.mem_filter.1 hx).1)
  · show 0 ≤ M (z - b)
    rw [← hLM, hιa, map_add, map_sum]
    refine add_nonneg hyL (Finset.sum_nonneg fun x hx => ?_)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hf0 x) (not_lt.1 (Finset.mem_filter.1 hx).2)
  · refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨hxG, hLx⟩ := Finset.mem_filter.1 hx
    by_cases hfx : f x = 0
    · rw [hfx, zero_smul]
      exact zero_mem _
    have hιr := hρ x hxG hfx
    exact smul_mem_hull_of_isExtremalRay ι hι himage L M hLM (by rw [hιr]; exact hGext x hxG)
      (by rwa [hιr]) (hf0 x)

/-- **Finitely many negative rays from a finite decomposition upstairs.** Let `ι : V → W` be an
injective linear map carrying a convex cone `K' ⊆ V` onto `K ∩ ι(V)` for a convex cone `K ⊆ W`,
and let `π : W → U` kill `ι(V)` and map `K` into a cone `K_U` containing no line. Suppose `ι`
maps extremal rays of `K'` to extremal rays of `K`, and `K = K_{L ≥ 0} + ∑_{x ∈ G} ℝ_{≥0} x` for a
linear form `L` and a finite set `G` of generators of extremal rays of `K` such that every
`x ∈ G` killed by `π` lies in `ι(V)`. Then for `M = L ∘ ι` the `M`-negative extremal rays of `K'`
are finitely many, each is spanned by a preimage of an element of `G`, and together with
`K'_{M ≥ 0}` they span `K'`. -/
private theorem finite_negative_rays_of_decomposition (ι : V →ₗ[ℝ] W)
    (hι : Function.Injective ι) (π : W →ₗ[ℝ] U) (K' : PointedCone ℝ V) (K : PointedCone ℝ W)
    (KU : PointedCone ℝ U) (hKU : KU.lineal = ⊥) (hπK : ∀ x ∈ K, π x ∈ KU)
    (hπι : ∀ v, π (ι v) = 0) (himage : ι '' (K' : Set V) = (K : Set W) ∩ Set.range ι)
    (hext : ∀ R, IsExtremalRay ℝ (K' : Set V) R → IsExtremalRay ℝ (K : Set W) (ι '' R))
    (L : W →ₗ[ℝ] ℝ) (M : V →ₗ[ℝ] ℝ) (hLM : ∀ v, L (ι v) = M v) (G : Finset W)
    (hGext : ∀ x ∈ G, IsExtremalRay ℝ (K : Set W) (ray x))
    (hdec : (K : Set W) = ((K : Set W) ∩ {z | 0 ≤ L z}) + (PointedCone.hull ℝ (G : Set W) : Set W))
    (hlift : ∀ x ∈ G, π x = 0 → x ∈ Set.range ι) :
    {R : Set V | IsExtremalRay ℝ (K' : Set V) R ∧ ∀ u ∈ R, u ≠ 0 → M u < 0}.Finite ∧
      (∀ R, IsExtremalRay ℝ (K' : Set V) R → (∀ u ∈ R, u ≠ 0 → M u < 0) →
        ∃ x ∈ G, ∃ r, ι r = x ∧ R = ray r) ∧
      (K' : Set V) = ((K' : Set V) ∩ {z | 0 ≤ M z}) +
        (PointedCone.hull ℝ
          (⋃₀ {R : Set V | IsExtremalRay ℝ (K' : Set V) R ∧ ∀ u ∈ R, u ≠ 0 → M u < 0}) :
            Set V) := by
  have hgen := exists_eq_ray_of_isExtremalRay_of_decomposition ι hext L M hLM G hGext hdec
  refine ⟨?_, hgen, ?_⟩
  · refine Set.Finite.of_finite_image ((G.finite_toSet.image ray).subset ?_)
      ((Set.image_injective.2 hι).injOn)
    rintro _ ⟨R, ⟨hR, hneg⟩, rfl⟩
    obtain ⟨x, hxG, r, rfl, rfl⟩ := hgen R hR hneg
    exact ⟨ι r, hxG, (image_ray ι r).symm⟩
  · ext z
    refine ⟨mem_add_hull_of_mem_of_decomposition ι hι π hKU hπK hπι himage L M hLM G hGext hdec
      hlift, ?_⟩
    rintro ⟨a, ⟨ha, -⟩, b, hb, rfl⟩
    refine K'.add_mem ha ((Submodule.span_le.2 ?_) hb)
    rintro u ⟨R, hR, hu⟩
    exact hR.1.1.1 hu

/-! ### Contracted curves -/

/-- A proper curve whose class has zero push-forward to a projective variety is contracted. -/
private theorem isContractedBy_of_pushforward_eq_zero {k : Type} [Field k] {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ] [LocallyOfFiniteType sZ]
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) (h : Y ⟶ Z) (hf : h ≫ sZ = sY) (C : ProperCurve sY)
    (h0 : NumericalCurveClasses.pushforward h hf (OneCycle.numericalClass sY (C.cycle ℝ)) = 0) :
    C.IsContractedBy h := by
  obtain ⟨L, hL, hLa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero h hf L hLa C ?_
  have := NumericalCurveClasses.degree_pushforward h hf L (OneCycle.numericalClass sY (C.cycle ℝ))
  rw [h0, map_zero, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at this
  exact_mod_cast this.symm

/-- The Weil divisor of the pull-back of a Cartier divisor along a dominant morphism has degree
zero on every contracted curve. -/
private theorem intersectionNumber_eq_zero_of_isPullback {k : Type} [Field k] {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sY] [IsSeparated sZ]
    [LocallyOfFiniteType sZ] (h : Y ⟶ Z) [IsDominant h] (hf : h ≫ sZ = sY)
    {T : Z.CartierDivisor} {T' : Y.CartierDivisor} (hT : MMP.Intersection.IsPullback h T T')
    {w : Divisor Y} (hw : MMP.Intersection.IsWeilDivisorOfCartier T' w) (C : ProperCurve sY)
    (hC : C.IsContractedBy h) (hq : (Divisor.toQDivisor w).IsQCartier) :
    (Divisor.toQDivisor w).intersectionNumber k sY C.ι C.dim_le hq = 0 := by
  have hwc := hw.isCartier
  rw [QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le w hwc hq]
  obtain ⟨e1⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨e2⟩ := MMP.ProgramBaseChange.nonempty_pullback_sheaf_iso h hT
  have := hwc.isInvertibleModule_divisorialSheaf
  have h0 := C.degree_pullback_eq_zero_of_isContractedBy h hf hC
    (MMP.CartierDivisor.sheaf T)
  rw [ProperCurve.degree, degreeOn_eq_of_iso k sY C.ι C.dim_le (e2 ≪≫ e1)] at h0
  exact_mod_cast h0

/-- The pull-back of a Cartier divisor along a dominant morphism has degree zero on every
contracted curve. -/
private theorem intersectionNumber_pullback_eq_zero {k : Type} [Field k] {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [QuasiCompact sY] [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (h : Y ⟶ Z) (hf : h ≫ sZ = sY) {H : Divisor Z} (hH : H.IsCartier)
    (hHf : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ H.supp)
    (C : ProperCurve sY) (hC : C.IsContractedBy h)
    (hq : (Divisor.toQDivisor (H.pullback hH hHf)).IsQCartier) :
    (Divisor.toQDivisor (H.pullback hH hHf)).intersectionNumber k sY C.ι C.dim_le hq = 0 := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sZ
  rw [QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le _ (hH.isCartier_pullback h hHf) hq]
  exact_mod_cast Divisor.degreeOn_pullback_eq_zero_of_isContractedBy h hf hH hHf C hC

/-- A prime divisor in the coefficient support of `D` lies in that of `D'` when
`Supp D ⊆ Supp D'`. -/
private theorem coeff_ne_zero_of_supp_le {R R' : Type*} [Zero R] [Zero R'] {X : Scheme.{0}}
    {D : DivisorWithCoeffs R X} {D' : DivisorWithCoeffs R' X} (hDD' : D.supp ≤ D'.supp)
    {P : MMP.Mori.PrimeDivisor X} (hP : D.coeff P ≠ 0) : D'.coeff P ≠ 0 := by
  have hη : P.genericPoint ∈ P.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨E, hE, hηE⟩ :=
    DivisorWithCoeffs.mem_supp_iff.mp (hDD' (DivisorWithCoeffs.support_subset_supp hP hη))
  rwa [MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hηE] at hE

/-! ### The klt reduction -/

/-- **Coefficient perturbation.** If `0 ≤ B ≤ 1`, `w ≥ 0` and `Supp ⌊B⌋ ⊆ Supp w ⊆ Supp B`, then
`B - δ w` is effective with all coefficients `< 1` for some rational `δ > 0`. -/
private theorem exists_pos_sub_smul_toQDivisor {X : Scheme.{0}} (B : QDivisor X) (w : Divisor X)
    (hB0 : ∀ P, 0 ≤ B.coeff P) (hB1 : ∀ P, B.coeff P ≤ 1) (hw0 : ∀ P, 0 ≤ w.coeff P)
    (hBw : ∀ P, B.roundDown.coeff P ≠ 0 → w.coeff P ≠ 0)
    (hwB : ∀ P, w.coeff P ≠ 0 → B.coeff P ≠ 0) :
    ∃ δ : ℚ, 0 < δ ∧ (∀ P, 0 ≤ (B - δ • Divisor.toQDivisor w).coeff P) ∧
      ∀ P, (B - δ • Divisor.toQDivisor w).coeff P < 1 := by
  have hcoeff : ∀ (δ : ℚ) P, (B - δ • Divisor.toQDivisor w).coeff P =
      B.coeff P - δ * (w.coeff P : ℚ) := fun δ P => rfl
  set S : ℚ := ∑ P ∈ w.support, (w.coeff P : ℚ) / B.coeff P
  have hS : 0 ≤ S := Finset.sum_nonneg fun P _ => div_nonneg (by exact_mod_cast hw0 P) (hB0 P)
  refine ⟨1 / (1 + S), by positivity, fun P => ?_, fun P => ?_⟩
  · rw [hcoeff]
    by_cases hP : P ∈ w.support
    · have hBP : 0 < B.coeff P :=
        lt_of_le_of_ne (hB0 P) (Ne.symm (hwB P (Finsupp.mem_support_iff.1 hP)))
      have hle : (w.coeff P : ℚ) / B.coeff P ≤ 1 + S := by
        have := Finset.single_le_sum (f := fun P => (w.coeff P : ℚ) / B.coeff P)
          (fun P _ => div_nonneg (by exact_mod_cast hw0 P) (hB0 P)) hP
        linarith
      rw [div_le_iff₀ hBP] at hle
      rw [sub_nonneg, one_div, inv_mul_le_iff₀ (by positivity)]
      linarith
    · rw [show w.coeff P = 0 from Finsupp.notMem_support_iff.1 hP]
      simpa using hB0 P
  · rw [hcoeff]
    have hδw : 0 ≤ 1 / (1 + S) * (w.coeff P : ℚ) :=
      mul_nonneg (by positivity) (by exact_mod_cast hw0 P)
    rcases (hB1 P).lt_or_eq with hlt | heq
    · linarith
    · have hP : P ∈ w.support := Finsupp.mem_support_iff.2 (hBw P (by
        rw [DivisorWithCoeffs.coeff_roundDown, heq]
        simp))
      have hwP : (0 : ℚ) < w.coeff P := by
        exact_mod_cast lt_of_le_of_ne (hw0 P) (Ne.symm (Finsupp.mem_support_iff.1 hP))
      have : 0 < 1 / (1 + S) * (w.coeff P : ℚ) := mul_pos (by positivity) hwP
      linarith

/-- On an integral proper scheme of dimension zero an invertible sheaf has a nonzero section. -/
private theorem finrank_ne_zero_of_dim_zero {κ : Type} [Field κ] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hd : topologicalKrullDim Z = 0) (P : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 P] :
    Module.finrank κ (cohomologyOverField κ g P 0) ≠ 0 := by
  have hall : ∀ x : Z, x = genericPoint Z := by
    intro x
    have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 (le_of_eq hd)
    let W : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let T : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have hTW : T ≤ W := hmin T fun _ _ => Set.mem_univ _
    have hx : IsGenericPoint x ⊤ := by
      change closure {x} = Set.univ
      exact Set.eq_univ_of_univ_subset hTW
    exact hx.eq (genericPoint_spec Z)
  obtain ⟨U, -, e, hxU, he⟩ := MMP.Intersection.exists_isTrivializingGenerator P
    (show genericPoint Z ∈ (⊤ : Z.Opens) from trivial)
  have hU : U = ⊤ := eq_top_iff.2 fun y _ => by rw [hall y]; exact hxU
  subst hU
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := (he ⊤ le_rfl).1 (a₁ := (1 : Γ(Z, ⊤))) (a₂ := 0) (by
      simp only [MMP.Intersection.modules_map_id, h0, smul_zero])
    exact one_ne_zero h1
  haveI : SheafOfModules.IsCoherent P :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z P
  haveI := finiteDimensional_cohomologyOverField_of_isProper κ g P 0
  haveI : Nontrivial (cohomologyOverField κ g P 0) :=
    @Equiv.nontrivial _ _ (cohomologyOverFieldZeroIsoSections κ g P).toLinearEquiv.toEquiv
      ⟨⟨e, 0, he0⟩⟩
  exact (Module.finrank_pos (R := κ) (M := cohomologyOverField κ g P 0)).ne'

/-- For a birational morphism of integral schemes, the residue field at the generic point of the
source has transcendence degree zero over the residue field at its image. -/
private theorem residueFieldTranscendenceDegree_genericPoint_eq_zero {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsIntegral Z] (h : Y ⟶ Z) (hb : IsBirationalMorphism h) :
    residueFieldTranscendenceDegree h (genericPoint Y) = 0 := by
  haveI : IsDominant h := hb.isDominant
  have hbij := hb.functionFieldMap_bijective
  have hn := AlgebraicGeometry.residueFieldMap_comp_genericResidueEquivOfDominant h
  have hsurj : Function.Surjective (h.residueFieldMap (genericPoint Y)).hom := by
    intro x
    obtain ⟨y, hy⟩ := hbij.surjective ((AlgebraicGeometry.genericResidueEquiv Y).symm x)
    refine ⟨AlgebraicGeometry.genericResidueEquivOfDominant h y, ?_⟩
    have := congrArg (fun φ => φ y) hn
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, hy]
    simp
  letI := (h.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have : Algebra.IsAlgebraic (Z.residueField (h (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj x
    exact isAlgebraic_algebraMap a
  unfold residueFieldTranscendenceDegree
  rw [_root_.trdeg_eq_zero]
  simp

/-- For a birational morphism `h` of projective varieties, the zero `ℚ`-divisor is `h`-big. -/
private theorem isRelativelyBig_zero {k : Type} [Field k] {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sY]
    [AlgebraicGeometry.IsProjectiveVariety k sZ] (h : Y ⟶ Z) (hf : h ≫ sZ = sY)
    (hb : IsBirationalMorphism h) : (0 : QDivisor Y).IsRelativelyBig h := by
  haveI : IsProper (h ≫ sZ) := hf ▸ (inferInstance : IsProper sY)
  haveI : IsProper h := IsProper.of_comp h sZ
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hfib : topologicalKrullDim (h.fiber (h (genericPoint Y))) = 0 := by
    rw [MMP.Flips.topologicalKrullDim_fiber_genericPoint,
      residueFieldTranscendenceDegree_genericPoint_eq_zero h hb]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, topologicalKrullDim Y = a := by
    have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
    have hbot : topologicalKrullDim Y ≠ ⊥ := fun hb =>
      ((Order.krullDim_eq_bot_iff.mp hb).false
        (TopologicalSpace.IrreducibleCloseds.closureSingleton (genericPoint Y))).elim
    induction hX : topologicalKrullDim Y using WithBot.recBotCoe with
    | bot => exact absurd hX hbot
    | coe a' =>
      have ha : a' ≠ ⊤ := by
        rintro rfl
        exact h1 hX
      lift a' to ℕ using ha
      exact ⟨a', rfl⟩
  have hb' : topologicalKrullDim (closure (Set.range h.base)) = a := by
    have := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range h k sY sZ hf
    rw [hfib, zero_add, ha] at this
    exact this.symm
  have hrank : relativeGenericRank h (0 : Divisor Y).divisorialSheaf ≠ 0 := by
    haveI := (Divisor.isCartier_zero (X := Y)).isInvertibleModule_divisorialSheaf
    haveI : IsProper (h.fiberToSpecResidueField (h (genericPoint Y))) :=
      inferInstanceAs (IsProper (Limits.pullback.snd h (Z.fromSpecResidueField _)))
    haveI : IsIntegral (h.fiber (h (genericPoint Y))) := MMP.Mori.isIntegral_generic_fibre h
    haveI := isLocallyNoetherian_fiber_of_locallyOfFiniteType h (h (genericPoint Y))
    rw [MMP.Mori.relativeGenericRank_eq_finrank_fibre h]
    exact finrank_ne_zero_of_dim_zero _ hfib _
  refine ⟨1, one_pos, 0, by simp, Divisor.isCartier_zero, a, a, ha, hb', 1 / 2, by norm_num, 0,
    fun m _ => ?_⟩
  rw [smul_zero, Nat.sub_self, pow_zero, mul_one]
  have : (1 : ℝ) ≤ relativeGenericRank h (0 : Divisor Y).divisorialSheaf := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hrank
  linarith

/-! ### Degrees on relative classes -/

/-- A linear form on `N₁(Y)` vanishing on the classes of the curves contracted by `h` vanishes on
the image of `N₁(Y/Z)`. -/
private theorem map_relativeToAbsolute_eq_zero {k : Type} [Field k] {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {h : Y ⟶ Z} (φ : NumericalCurveClasses sY →ₗ[ℝ] ℝ)
    (hφ : ∀ C : ProperCurve sY, C.IsContractedBy h →
      φ (OneCycle.numericalClass sY (C.cycle ℝ)) = 0)
    (z : RelativeNumericalCurveClasses sY h) : φ (relativeToAbsolute sY h z) = 0 := by
  obtain ⟨⟨Zc, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sY h z
  rw [isNaturalRelativeMap_relativeToAbsolute sY h ⟨Zc, hZ⟩]
  change φ (OneCycle.numericalClass sY Zc) = 0
  conv_lhs => rw [← Finsupp.sum_single Zc]
  rw [map_finsuppSum, map_finsuppSum]
  refine Finset.sum_eq_zero fun C hC => ?_
  show φ (OneCycle.numericalClass sY (Finsupp.single C (Zc C))) = 0
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  change Zc C • φ (OneCycle.numericalClass sY (C.cycle ℝ)) = 0
  rw [hφ C (hZ hC), smul_zero]

/-- Intersection numbers with proper curves are invariant under `ℚ`-linear equivalence. -/
private theorem intersectionNumber_eq_of_qLinearlyEquivalent {k : Type} [Field k]
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] (hQ : ∀ D : QDivisor Y, D.IsQCartier)
    (C : ProperCurve sY) {A B : QDivisor Y} (hAB : A.QLinearlyEquivalent B) :
    A.intersectionNumber k sY C.ι C.dim_le (hQ A) =
      B.intersectionNumber k sY C.ι C.dim_le (hQ B) := by
  obtain ⟨m, hm, φ, hφ⟩ := hAB
  have hdc := Divisor.isCartier_principalDivisor φ
  have hP : (Divisor.toQDivisor (principalDivisor φ)).intersectionNumber k sY C.ι C.dim_le
      (hQ _) = 0 := by
    rw [QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le _ hdc]
    have := hdc.isInvertibleModule_divisorialSheaf
    have := (Divisor.isCartier_zero (X := Y)).isInvertibleModule_divisorialSheaf
    have h1 : (principalDivisor φ).degreeOn k sY C.ι C.dim_le hdc =
        (0 : Divisor Y).degreeOn k sY C.ι C.dim_le Divisor.isCartier_zero :=
      degreeOn_eq_of_iso k sY C.ι C.dim_le
        (Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso
    rw [h1, Divisor.degreeOn_zero' k sY C.ι C.dim_le, Int.cast_zero]
  have hsmul := MMP.Fourfold.intersectionNumber_smul sY C.ι C.dim_le (A - B) (hQ _) (m : ℚ)
    (hQ _)
  have heq : (m : ℚ) • (A - B) = Divisor.toQDivisor (principalDivisor φ) := by
    rw [← hφ, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  rw [MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le (hQ _) (hQ _) heq, hP] at hsmul
  have hsub := QDivisor.intersectionNumber_add' k sY C.ι C.dim_le B (A - B) (hQ B) (hQ _) (hQ _)
  rw [MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le (hQ _) (hQ A)
    (add_sub_cancel B A)] at hsub
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hsub, (mul_eq_zero.1 hsmul.symm).resolve_left hm', add_zero]

/-- **The klt reduction.** If `(Y, B)` is dlt on a `ℚ`-factorial `Y`, `w ≥ 0` and
`Supp ⌊B⌋ ⊆ Supp w ⊆ Supp B`, then `(Y, B - δ w)` is an effective klt pair for some rational
`δ > 0`. -/
private theorem exists_pos_isKltPair_sub_smul {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    (hQ : ∀ D : QDivisor Y, D.IsQCartier) {B : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY B)
    {w : Divisor Y} (hw0 : ∀ P, 0 ≤ w.coeff P) (hBw : B.roundDown.supp ≤ w.supp)
    (hwB : w.supp ≤ B.supp) :
    ∃ δ : ℚ, 0 < δ ∧ (B - δ • Divisor.toQDivisor w).IsEffective ∧
      MMP.Fourfold.IsKltPair sY (B - δ • Divisor.toQDivisor w) := by
  obtain ⟨δ, hδ, hB'0, hB'1⟩ :=
    exists_pos_sub_smul_toQDivisor B w hB.1.2.1 hB.2.1 hw0
      (fun P hP => coeff_ne_zero_of_supp_le hBw hP) (fun P hP => coeff_ne_zero_of_supp_le hwB hP)
  have hB'e : (B - δ • Divisor.toQDivisor w).IsEffective := hB'0
  refine ⟨δ, hδ, hB'e, (MMP.Intersection.IsDltPair.of_le sY hB
    (DivisorWithCoeffs.isEffective_iff_nonneg.1 hB'e) (Finsupp.le_def.2 fun P => ?_)
    (hQ _)).isKltPair_of_forall_coeff_lt_one hB'1⟩
  change B.coeff P - δ * (w.coeff P : ℚ) ≤ B.coeff P
  have : (0 : ℚ) ≤ δ * (w.coeff P : ℚ) := mul_nonneg hδ.le (by exact_mod_cast hw0 P)
  linarith

/-- On a curve `C` contracted by `h`, `D' · C + A · C = D · C` whenever
`D' + A = D - δ h^*H + T_Y` with `T_Y` `ℚ`-linearly equivalent to a multiple of a pull-back
from `Z`. -/
private theorem intersectionNumber_add_eq_of_isContractedBy {k : Type} [Field k]
    {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [AlgebraicGeometry.IsProjectiveVariety k sY]
    [AlgebraicGeometry.IsProjectiveVariety k sZ] (h : Y ⟶ Z) [IsDominant h] (hf : h ≫ sZ = sY)
    (hQ : ∀ D : QDivisor Y, D.IsQCartier) {H : Divisor Z} (hH : H.IsCartier)
    (hHf : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ H.supp) {c : ℚ}
    {T₀ : Z.CartierDivisor} {T₀' : Y.CartierDivisor} {w₀ : Divisor Y}
    (hT₀ : MMP.Intersection.IsPullback h T₀ T₀')
    (hw₀ : MMP.Intersection.IsWeilDivisorOfCartier T₀' w₀) {TY : QDivisor Y}
    (hTY : TY.QLinearlyEquivalent (c • Divisor.toQDivisor w₀)) {D D' A : QDivisor Y} {δ : ℚ}
    (e : D' + A = D + ((-δ) • Divisor.toQDivisor (H.pullback hH hHf) + TY))
    (C : ProperCurve sY) (hC : C.IsContractedBy h) :
    D'.intersectionNumber k sY C.ι C.dim_le (hQ _) +
        A.intersectionNumber k sY C.ι C.dim_le (hQ _) =
      D.intersectionNumber k sY C.ι C.dim_le (hQ _) := by
  have hw' := intersectionNumber_pullback_eq_zero h hf hH hHf C hC (hQ _)
  have hw₀' := intersectionNumber_eq_zero_of_isPullback h hf hT₀ hw₀ C hC (hQ _)
  have hTY' := intersectionNumber_eq_of_qLinearlyEquivalent hQ C hTY
  rw [MMP.Fourfold.intersectionNumber_smul sY C.ι C.dim_le _ (hQ _) c (hQ _), hw₀',
    mul_zero] at hTY'
  have hsm := MMP.Fourfold.intersectionNumber_smul sY C.ι C.dim_le
    (Divisor.toQDivisor (H.pullback hH hHf)) (hQ _) (-δ) (hQ _)
  rw [hw', mul_zero] at hsm
  have h1 := QDivisor.intersectionNumber_add' k sY C.ι C.dim_le D
    ((-δ) • Divisor.toQDivisor (H.pullback hH hHf) + TY) (hQ _) (hQ _) (hQ _)
  have h2 := QDivisor.intersectionNumber_add' k sY C.ι C.dim_le
    ((-δ) • Divisor.toQDivisor (H.pullback hH hHf)) TY (hQ _) (hQ _) (hQ _)
  rw [← QDivisor.intersectionNumber_add' k sY C.ι C.dim_le _ _ (hQ _) (hQ _) (hQ _),
    MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le (hQ _) (hQ _) e, h1, h2, hsm, hTY']
  ring

/-- **Descent of a finite decomposition.** If `NE̅(Y) = NE̅(Y)_{L ≥ 0} + ∑_{C ∈ S} ℝ_{≥0} [C]`
for finitely many rational curves `C` spanning extremal rays and a linear form `L` agreeing with
`D` on the curves contracted by `h`, then the `D`-negative extremal rays of `NE̅(Y/Z)` are
finitely many, each spanned by a contracted rational curve, and together with
`NE̅(Y/Z)_{D ≥ 0}` they span `NE̅(Y/Z)`. -/
private theorem exists_finite_isExtremalRay_of_closedConeOfCurves_eq {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sY] (h : Y ⟶ Z)
    [IsDominant h] (hf : h ≫ sZ = sY) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    [DecidableEq (NumericalCurveClasses sY)] {D : QDivisor Y} (hD : D.IsQCartier)
    (L : NumericalCurveClasses sY →ₗ[ℝ] ℝ)
    (hL : ∀ C : ProperCurve sY, C.IsContractedBy h → L (OneCycle.numericalClass sY (C.cycle ℝ)) =
      QDivisor.curveForm sY D hD (OneCycle.numericalClass sY (C.cycle ℝ)))
    (S : Finset (ProperCurve sY))
    (hS : ∀ C ∈ S, IsRationalCurve sY
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set Y))) ∧
      IsExtremalRay ℝ (closedConeOfCurves sY : Set (NumericalCurveClasses sY))
        {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sY (C.cycle ℝ) = w})
    (hdec : (closedConeOfCurves sY : Set (NumericalCurveClasses sY)) =
      ((closedConeOfCurves sY : Set (NumericalCurveClasses sY)) ∩ {z | 0 ≤ L z}) +
        (PointedCone.hull ℝ
          ((S.image fun C : ProperCurve sY => OneCycle.numericalClass sY (C.cycle ℝ) :
            Finset (NumericalCurveClasses sY)) : Set (NumericalCurveClasses sY)) : Set _)) :
    ∃ 𝓡 : Set (Set (RelativeNumericalCurveClasses sY h)), 𝓡.Finite ∧
      (∀ R, R ∈ 𝓡 ↔
        IsExtremalRay ℝ (relativeClosedConeOfCurves sY h : Set _) R ∧
          ∀ u ∈ R, u ≠ 0 → QDivisor.curveForm sY D hD (relativeToAbsolute sY h u) < 0) ∧
      (∀ R ∈ 𝓡, ∃ (C : ProperCurve sY) (hC : C.IsContractedBy h),
        IsRationalCurve sY
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set Y))) ∧
        R = {v | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = v}) ∧
      (relativeClosedConeOfCurves sY h : Set (RelativeNumericalCurveClasses sY h)) =
        ((relativeClosedConeOfCurves sY h : Set (RelativeNumericalCurveClasses sY h)) ∩
            {z | 0 ≤ QDivisor.curveForm sY D hD (relativeToAbsolute sY h z)}) +
          (PointedCone.hull ℝ (⋃₀ 𝓡) : Set (RelativeNumericalCurveClasses sY h)) := by
  have : AlgebraicGeometry.IsProjectiveVariety k sZ := hZp
  set ι := relativeToAbsolute sY h
  have hι : Function.Injective ι := (existsUnique_isNaturalRelativeMap_and_injective sY h).2 _
    (isNaturalRelativeMap_relativeToAbsolute sY h)
  set M : RelativeNumericalCurveClasses sY h →ₗ[ℝ] ℝ := (QDivisor.curveForm sY D hD).comp ι
  have hLM : ∀ v, L (ι v) = M v := by
    intro v
    have := map_relativeToAbsolute_eq_zero (h := h) (L - QDivisor.curveForm sY D hD)
      (fun C hC => by rw [LinearMap.sub_apply, hL C hC, sub_self]) v
    rwa [LinearMap.sub_apply, sub_eq_zero] at this
  have hιC : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy h),
      ι (C.relativeClass h hC) = OneCycle.numericalClass sY (C.cycle ℝ) := fun C hC =>
    isNaturalRelativeMap_relativeToAbsolute sY h ⟨C.cycle ℝ, C.cycle_mem_relativeOneCycles hC⟩
  have hπι : ∀ v, NumericalCurveClasses.pushforward h hf (ι v) = 0 := fun v =>
    LinearMap.mem_ker.1 (range_relativeToAbsolute_le_ker_pushforward h hf ⟨v, rfl⟩)
  obtain ⟨hfin, hgen, hrel⟩ := finite_negative_rays_of_decomposition ι hι
    (NumericalCurveClasses.pushforward h hf) (relativeClosedConeOfCurves sY h)
    (closedConeOfCurves sY) (closedConeOfCurves sZ) (lineal_closedConeOfCurves_eq_bot sZ)
    (fun x hx => image_closedConeOfCurves_subset h hf
      (NumericalCurveClasses.isNumericalPushforward_pushforward h hf) ⟨x, hx, rfl⟩)
    hπι (image_relativeClosedConeOfCurves_eq_inter_range sY sZ h hf)
    (fun R hR => isExtremalRay_image_relativeToAbsolute sY sZ h hf hR) L M hLM _
    (fun x hx => by
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hx
      exact (hS C hC).2)
    hdec
    (fun x hx hx0 => by
      obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨_, hιC C (isContractedBy_of_pushforward_eq_zero hZp h hf C hx0)⟩)
  have hMι : ∀ u, QDivisor.curveForm sY D hD (ι u) = M u := fun u => rfl
  simp only [hMι]
  set 𝓡 := {R | IsExtremalRay ℝ (relativeClosedConeOfCurves sY h : Set _) R ∧
    ∀ u ∈ R, u ≠ 0 → M u < 0}
  have hgen' : ∀ R ∈ 𝓡, ∃ (C : ProperCurve sY) (hC : C.IsContractedBy h),
      IsRationalCurve sY
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set Y))) ∧
      R = {v | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = v} := by
    rintro R ⟨hR, hneg⟩
    obtain ⟨x, hx, r, hrx, hRr⟩ := hgen R hR hneg
    obtain ⟨C, hCS, rfl⟩ := Finset.mem_image.1 hx
    have hC := isContractedBy_of_pushforward_eq_zero hZp h hf C (hrx ▸ hπι r)
    have hr : r = C.relativeClass h hC := hι (hrx.trans (hιC C hC).symm)
    refine ⟨C, hC, (hS C hCS).1, ?_⟩
    rw [hRr, hr]
    rfl
  exact ⟨𝓡, hfin, fun R => Iff.rfl, hgen', hrel⟩

end MMP.FourfoldProofs.FourfoldProjectiveSupportSandwichFiniteRaysProof

@[expose] public section

namespace MMP.Fourfold

open MMP.Mori

open MMP.FourfoldProofs.FourfoldProjectiveSupportSandwichFiniteRaysProof in
/-- **Finitely many negative rays under a support sandwich.** Let `h : Y ⟶ Z` be a projective
birational morphism of normal projective varieties over an algebraically closed field `k` of
characteristic zero, with `Y` `ℚ`-factorial and canonical divisor `K`, let `(Y, B)` be dlt, and
let `H` be an effective Cartier divisor on `Z`, no generic point of `Y` mapping into its
support, whose pull-back satisfies `Supp ⌊B⌋ ⊆ Supp h^*H ⊆ Supp B`. Then `K + B` is `ℚ`-Cartier
and there is a finite set `𝓡` of subsets of `N₁(Y/Z)` such that

* `𝓡` consists exactly of the extremal rays `R` of `NE̅(Y/Z)` with `((K + B) · u) < 0` for every
  `0 ≠ u ∈ R`;
* every `R ∈ 𝓡` is `ℝ_{≥0} [C]` for a rational curve `C` contracted by `h`;
* `NE̅(Y/Z) = NE̅(Y/Z)_{(K + B) ≥ 0} + ∑_{R ∈ 𝓡} R`. -/
@[mmp "lem_fourfold_projective_support_sandwich_finite_rays"]
public theorem exists_finite_isExtremalRay_of_support_roundDown_subset_pullback
    {k : Type} [Field k] {Y Z : Scheme.{0}}
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (h : Y ⟶ Z)
    (hs : IsProjectiveSetting k sY sZ h) (hhp : IsProjectiveMorphism h)
    (hhb : IsBirationalMorphism h) (hZ : IsNormalVariety k sZ) (hY : IsQFactorial sY)
    {K : Divisor Y} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY B)
    {H : Divisor Z} (hH : H.IsCartier) (hHe : H.IsEffective)
    (hHf : ∀ W : irreducibleComponents Y, h (componentGenericPoint Y W) ∉ H.supp)
    (hBw : B.roundDown.supp ≤ (H.pullback hH hHf).supp)
    (hwB : (H.pullback hH hHf).supp ≤ B.supp) :
    ∃ hKB : (Divisor.toQDivisor K + B).IsQCartier,
      ∃ 𝓡 : Set (Set (RelativeNumericalCurveClasses sY h)), 𝓡.Finite ∧
        (∀ R, R ∈ 𝓡 ↔
          IsExtremalRay ℝ (relativeClosedConeOfCurves sY h : Set _) R ∧
            ∀ u ∈ R, u ≠ 0 →
              QDivisor.curveForm sY (Divisor.toQDivisor K + B) hKB
                (relativeToAbsolute sY h u) < 0) ∧
        (∀ R ∈ 𝓡, ∃ (C : ProperCurve sY) (hC : C.IsContractedBy h),
          IsRationalCurve sY
            (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set Y))) ∧
          R = {v | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = v}) ∧
        (relativeClosedConeOfCurves sY h : Set (RelativeNumericalCurveClasses sY h)) =
          ((relativeClosedConeOfCurves sY h : Set (RelativeNumericalCurveClasses sY h)) ∩
              {z | 0 ≤ QDivisor.curveForm sY (Divisor.toQDivisor K + B) hKB
                (relativeToAbsolute sY h z)}) +
            (PointedCone.hull ℝ (⋃₀ 𝓡) : Set (RelativeNumericalCurveClasses sY h)) := by
  classical
  obtain ⟨hk, hc0, hYp, hZp, hf⟩ := hs
  haveI := hk
  haveI := hc0
  haveI : AlgebraicGeometry.IsProjectiveVariety k sY := hYp
  haveI : AlgebraicGeometry.IsProjectiveVariety k sZ := hZp
  haveI : IsIntegral Z := hZp.toIsVariety.toIsIntegral
  haveI : IsDominant h := hhb.isDominant
  have hQ := MMP.Fourfold.isQCartier_of_isQFactorial sY hY
  obtain ⟨n, hKn⟩ := hK
  refine ⟨hQ _, ?_⟩
  set w := H.pullback hH hHf
  have hw0 : ∀ P, 0 ≤ w.coeff P := fun P =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hH (V := ⊤)
      (fun Q _ => hHe Q) (Divisor.isPullback_pullback hH hHf) P
      ((P.genericPoint_mem_iff _).mp trivial)
  obtain ⟨δ, -, hB'e, hB'klt⟩ := exists_pos_isKltPair_sub_smul sY hQ hB hw0 hBw hwB
  set B' := B - δ • Divisor.toQDivisor w with hB'
  obtain ⟨A', TY, hA', -, ⟨c, T₀, T₀', w₀, hT₀, hw₀, hTY⟩, heff, hklt⟩ :=
    QDivisor.IsRelativelyBig.exists_isKltPair_add_pullback_sub_isAmple sY sZ hY h hf
      (isRelativelyBig_zero sY sZ h hf hhb) DivisorWithCoeffs.isEffective_zero {B'}
      (by simpa using hB'e) (by simpa using DivisorWithCoeffs.isEffective_iff_nonneg.1 hB'e)
      (by simpa using hB'klt)
  set Cb := B' + TY - A' with hCb
  have hCeff : Cb.IsEffective := heff B' (subset_convexHull ℚ _ (by simp))
  have hCklt : MMP.Mori.IsKltPair sY n K Cb :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hKn (hklt B' (by simp)).1.1).mp
      (hklt B' (by simp)).1
  obtain ⟨S, hS, hdec⟩ :=
    exists_finset_isRationalCurve_closedConeOfCurves_eq hCklt hCeff one_pos hA'
  have e : Divisor.toQDivisor K + Cb + A' =
      (Divisor.toQDivisor K + B) + ((-δ) • Divisor.toQDivisor w + TY) := by
    rw [hCb, hB', neg_smul]
    abel
  set L : NumericalCurveClasses sY →ₗ[ℝ] ℝ :=
    QDivisor.curveForm sY (Divisor.toQDivisor K + Cb) (hQ _) + QDivisor.curveForm sY A' (hQ _)
  have hset : {z | 0 ≤ L z} = {z | 0 ≤ QDivisor.curveForm sY (Divisor.toQDivisor K + Cb)
      hCklt.1.2.2 z + 1 * QDivisor.curveForm sY A' (hQ _) z} := by
    ext z
    simp only [Set.mem_setOf_eq, one_mul]
    exact Iff.rfl
  refine exists_finite_isExtremalRay_of_closedConeOfCurves_eq sY sZ h hf hZp (hQ _) L
    (fun C hC => ?_) S (fun C hC => ⟨(hS C hC).1, (hS C hC).2.2.2⟩)
    (by rw [Finset.coe_image, hset]; exact hdec)
  simp only [L, LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle sY]
  exact_mod_cast intersectionNumber_add_eq_of_isContractedBy h hf hQ hH hHf hT₀ hw₀ hTY e C hC

end MMP.Fourfold

end