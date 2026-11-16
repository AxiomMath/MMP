module

public import MMP.AlgebraicTopology.Triangulation.OrderComplexTriangulation

/-!
# The lifting step of the triangulation theorem

Let `h₀ : |Δ| → B` be a standard triangulation of `B ⊆ ℝ^σ` and, over each open simplex `s`,
let `ζ_{s,0} < ζ_{s,1} < ⋯` be finitely many functions continuous on the closed simplex, whose
restrictions to each face `t` are functions of the family of `t`. A closed set `S ⊆ ℝ^σ × ℝ`
which is a union of graphs `{(h₀ y, ζ_{s,j}(y))}` and bands `{(h₀ y, t) : ζ_{s,j}(y) < t <
ζ_{s,j+1}(y)}` over the open simplices is the union of a finite cell complex with radial
structures: a graph cell is the image of the closed simplex, coned from its barycentre; a band
cell is the image of the convex region `|v| ≤ min_F d_F(y)` over the closed simplex, where `F`
runs over the faces on which the band degenerates and `d_F` is the total weight off `F`, by the
vertical reparametrisation `(y, v) ↦ (h₀ y, mid(y) + v · halfwidth(y) / min_F d_F(y))`. The
order complex of these cells is a standard triangulation of `S`, compatible with every set that
is a union of graphs and bands.

## Main definitions

* `MMP.graphCell`, `MMP.bandCell`: graphs and bands over an open
  simplex.
* `MMP.bandMap`: the vertical reparametrisation of the band model.

## Main results

* `MMP.exists_isStdTriangulation_of_cells`: the lifting step.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], Theorem 9.2.1.
-/

@[expose] public section

open Set Filter Topology

namespace MMP

/-- `optionCons` is injective in both arguments jointly. -/
theorem optionCons_injective {σ : Type*} {a a' : σ → ℝ} {t t' : ℝ}
    (h : optionCons a t = optionCons a' t') : a = a' ∧ t = t' :=
  ⟨funext fun i ↦ congrFun h (some i), congrFun h none⟩

section Maps

variable {σ ν : Type*} [Fintype ν] [DecidableEq ν]

/-- The graph of `ζ` over the open simplex of `s`, through `h₀`. -/
def graphCell (h₀ : (ν → ℝ) → σ → ℝ) (ζ : (ν → ℝ) → ℝ) (s : Finset ν) : Set (Option σ → ℝ) :=
  (fun y ↦ optionCons (h₀ y) (ζ y)) '' openStd s

/-- The band between `lo` and `hi` over the open simplex of `s`, through `h₀`. -/
def bandCell (h₀ : (ν → ℝ) → σ → ℝ) (lo hi : (ν → ℝ) → ℝ) (s : Finset ν) :
    Set (Option σ → ℝ) :=
  {x | ∃ y ∈ openStd s, ∃ t, lo y < t ∧ t < hi y ∧ optionCons (h₀ y) t = x}

/-- The closed band between `lo` and `hi` over the closed simplex of `s`. -/
def closedBandCell (h₀ : (ν → ℝ) → σ → ℝ) (lo hi : (ν → ℝ) → ℝ) (s : Finset ν) :
    Set (Option σ → ℝ) :=
  {x | ∃ y ∈ closedStd s, ∃ t, lo y ≤ t ∧ t ≤ hi y ∧ optionCons (h₀ y) t = x}

/-- The vertical reparametrisation of the band model: `(y, v)` goes to the point over `h₀ y` at
height `mid(y) + v · halfwidth(y) / g(y)`. -/
noncomputable def bandMap (h₀ : (ν → ℝ) → σ → ℝ) (lo hi g : (ν → ℝ) → ℝ) (z : (ν → ℝ) × ℝ) :
    Option σ → ℝ :=
  optionCons (h₀ z.1) ((lo z.1 + hi z.1) / 2 + z.2 * ((hi z.1 - lo z.1) / 2 / g z.1))

/-- If `|v| ≤ g` and `0 ≤ w`, then `|v * (w / g)| ≤ w`. -/
theorem abs_mul_div_le_of_abs_le {v g w : ℝ} (hw : 0 ≤ w) (hv : |v| ≤ g) : |v * (w / g)| ≤ w := by
  rcases eq_or_lt_of_le ((abs_nonneg v).trans hv) with hg | hg
  · rw [← hg, div_zero, mul_zero, abs_zero]
    exact hw
  · rw [abs_mul, abs_div, abs_of_nonneg hw, abs_of_pos hg, mul_div_assoc', div_le_iff₀ hg]
    exact mul_comm w g ▸ mul_le_mul_of_nonneg_right hv hw

/-- If `|v| < g` and `0 < w`, then `|v * (w / g)| < w`. -/
theorem abs_mul_div_lt_of_abs_lt {v g w : ℝ} (hw : 0 < w) (hv : |v| < g) : |v * (w / g)| < w := by
  have hg : 0 < g := (abs_nonneg v).trans_lt hv
  rw [abs_mul, abs_div, abs_of_pos hw, abs_of_pos hg, mul_div_assoc', div_lt_iff₀ hg]
  exact mul_comm w g ▸ mul_lt_mul_of_pos_right hv hw

omit [Fintype ν] [DecidableEq ν] in
/-- `bandMap` sends the height `(t - mid) · g / halfwidth` back to the height `t`. -/
theorem bandMap_mk_div {h₀ : (ν → ℝ) → σ → ℝ} {lo hi g : (ν → ℝ) → ℝ} {y : ν → ℝ} {t : ℝ}
    (hg : g y ≠ 0) (hd : hi y - lo y ≠ 0) :
    bandMap h₀ lo hi g (y, (t - (lo y + hi y) / 2) * g y / ((hi y - lo y) / 2)) =
      optionCons (h₀ y) t := by
  simp only [bandMap]
  congr 1
  field_simp
  ring

variable {s : Finset ν} (hs : s.Nonempty) {𝓕 : Finset (Finset ν)} (h𝓕 : 𝓕.Nonempty)
  (h𝓕e : ∅ ∈ 𝓕) (h𝓕s : ∀ F ∈ 𝓕, ¬ s ⊆ F) {h₀ : (ν → ℝ) → σ → ℝ} {lo hi : (ν → ℝ) → ℝ}
  (hh₀ : ContinuousOn h₀ (closedStd s)) (hinj : InjOn h₀ (closedStd s))
  (hlo : ContinuousOn lo (closedStd s)) (hhi : ContinuousOn hi (closedStd s))
  (hle : ∀ y ∈ closedStd s, lo y ≤ hi y)
  (hdeg : ∀ y ∈ closedStd s, lo y = hi y ↔ faceMin s 𝓕 h𝓕 y = 0)

include hs h𝓕e h𝓕s hle hdeg

/-- On the band model, the height of `bandMap` lies between `lo` and `hi`. -/
theorem bandMap_mem {z : (ν → ℝ) × ℝ} (hz : z ∈ bandModel s 𝓕 h𝓕) :
    lo z.1 ≤ (lo z.1 + hi z.1) / 2 + z.2 * ((hi z.1 - lo z.1) / 2 / faceMin s 𝓕 h𝓕 z.1) ∧
      (lo z.1 + hi z.1) / 2 + z.2 * ((hi z.1 - lo z.1) / 2 / faceMin s 𝓕 h𝓕 z.1) ≤ hi z.1 := by
  have h := abs_mul_div_le_of_abs_le (div_nonneg (sub_nonneg.2 (hle z.1 hz.1)) zero_le_two) hz.2
  constructor <;> linarith [abs_le.1 h]

include hinj in
/-- `bandMap` is injective on the band model. -/
theorem injOn_bandMap : InjOn (bandMap h₀ lo hi (faceMin s 𝓕 h𝓕)) (bandModel s 𝓕 h𝓕) := by
  rintro ⟨y, v⟩ hz ⟨y', v'⟩ hz' h
  obtain ⟨h1, h2⟩ := optionCons_injective h
  obtain rfl : y = y' := hinj hz.1 hz'.1 h1
  refine Prod.ext rfl ?_
  simp only at h2 ⊢
  by_cases hg : faceMin s 𝓕 h𝓕 y = 0
  · have hv : |v| ≤ 0 := hg ▸ hz.2
    have hv' : |v'| ≤ 0 := hg ▸ hz'.2
    rw [abs_nonpos_iff.1 hv, abs_nonpos_iff.1 hv']
  · have hlt : lo y < hi y := lt_of_le_of_ne (hle y hz.1) fun h ↦ hg ((hdeg y hz.1).1 h)
    have hw : (hi y - lo y) / 2 / faceMin s 𝓕 h𝓕 y ≠ 0 :=
      div_ne_zero (div_ne_zero (sub_ne_zero.2 hlt.ne') two_ne_zero) hg
    exact mul_right_cancel₀ hw (add_left_cancel h2)

include hh₀ hlo hhi in
/-- `bandMap` is continuous on the band model. -/
theorem continuousOn_bandMap :
    ContinuousOn (bandMap h₀ lo hi (faceMin s 𝓕 h𝓕)) (bandModel s 𝓕 h𝓕) := by
  have hfst : MapsTo Prod.fst (bandModel s 𝓕 h𝓕) (closedStd s) := fun z hz ↦ hz.1
  have hg : Continuous (faceMin s 𝓕 h𝓕) :=
    Continuous.finset_inf'_apply h𝓕 fun F _ ↦ continuous_finsetSum (s \ F) fun u _ ↦
      continuous_apply u
  have hlo' := hlo.comp continuousOn_fst hfst
  have hhi' := hhi.comp continuousOn_fst hfst
  have hmid : ContinuousOn (fun z : (ν → ℝ) × ℝ ↦ (lo z.1 + hi z.1) / 2) (bandModel s 𝓕 h𝓕) :=
    (hlo'.add hhi').div_const 2
  have hsnd : ContinuousOn (fun z : (ν → ℝ) × ℝ ↦
      (lo z.1 + hi z.1) / 2 + z.2 * ((hi z.1 - lo z.1) / 2 / faceMin s 𝓕 h𝓕 z.1))
      (bandModel s 𝓕 h𝓕) := by
    intro z₀ hz₀
    by_cases hg0 : faceMin s 𝓕 h𝓕 z₀.1 = 0
    · have hwid : (hi z₀.1 - lo z₀.1) / 2 = 0 := by
        rw [(hdeg z₀.1 hz₀.1).2 hg0, sub_self, zero_div]
      have hr : Tendsto (fun z : (ν → ℝ) × ℝ ↦ z.2 * ((hi z.1 - lo z.1) / 2 /
          faceMin s 𝓕 h𝓕 z.1)) (𝓝[bandModel s 𝓕 h𝓕] z₀) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ (a := fun z ↦ (hi z.1 - lo z.1) / 2) ?_
        · filter_upwards [self_mem_nhdsWithin] with z hz
          rw [Real.norm_eq_abs]
          exact abs_mul_div_le_of_abs_le (div_nonneg (sub_nonneg.2 (hle z.1 hz.1)) zero_le_two) hz.2
        · have := ((hhi'.sub hlo').div_const 2) z₀ hz₀
          simp only [ContinuousWithinAt, Pi.sub_apply, Function.comp] at this
          rwa [hwid] at this
      have hval : (lo z₀.1 + hi z₀.1) / 2 + z₀.2 * ((hi z₀.1 - lo z₀.1) / 2 /
          faceMin s 𝓕 h𝓕 z₀.1) = (lo z₀.1 + hi z₀.1) / 2 + 0 := by
        rw [hwid, zero_div, mul_zero]
      rw [ContinuousWithinAt, hval]
      exact (hmid z₀ hz₀).tendsto.add hr
    · exact (hmid z₀ hz₀).add (continuousWithinAt_snd.mul
        ((((hhi'.sub hlo').div_const 2) z₀ hz₀).div (hg.comp continuous_fst).continuousWithinAt
          hg0))
  exact continuous_optionCons.comp_continuousOn ((hh₀.comp continuousOn_fst hfst).prodMk hsnd)

/-- `bandMap` maps the band model onto the closed band between `lo` and `hi`. -/
theorem bandMap_image :
    bandMap h₀ lo hi (faceMin s 𝓕 h𝓕) '' bandModel s 𝓕 h𝓕 = closedBandCell h₀ lo hi s := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := bandMap_mem hs h𝓕 h𝓕e h𝓕s hle hdeg hz
    exact ⟨z.1, hz.1, _, h1, h2, rfl⟩
  · rintro ⟨y, hy, t, h1, h2, rfl⟩
    have hg0 := faceMin_nonneg h𝓕 hy
    by_cases hg : faceMin s 𝓕 h𝓕 y = 0
    · have heq := (hdeg y hy).2 hg
      refine ⟨(y, 0), ⟨hy, by simp [hg]⟩, ?_⟩
      simp only [bandMap, zero_mul, add_zero]
      congr 1
      linarith
    · have hlt : lo y < hi y := lt_of_le_of_ne (hle y hy) fun h ↦ hg ((hdeg y hy).1 h)
      have hw : 0 < (hi y - lo y) / 2 := by linarith
      have hgp : 0 < faceMin s 𝓕 h𝓕 y := lt_of_le_of_ne hg0 (Ne.symm hg)
      refine ⟨(y, (t - (lo y + hi y) / 2) * faceMin s 𝓕 h𝓕 y / ((hi y - lo y) / 2)),
        ⟨hy, ?_⟩, ?_⟩
      · simp only
        rw [abs_div, abs_mul, abs_of_pos hw, abs_of_pos hgp, div_le_iff₀ hw]
        have : |t - (lo y + hi y) / 2| ≤ (hi y - lo y) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
        nlinarith
      · exact bandMap_mk_div hgp.ne' (by linarith)

/-- `bandMap` maps the part of the band model where `bandGauge < 1` onto the open band between
`lo` and `hi` over the open simplex. -/
theorem bandMap_image_lt :
    bandMap h₀ lo hi (faceMin s 𝓕 h𝓕) '' (bandModel s 𝓕 h𝓕 ∩
      {z | bandGauge s hs 𝓕 h𝓕 z < 1}) = bandCell h₀ lo hi s := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hy, hv⟩ := (bandModel_inter_lt_iff hs h𝓕 h𝓕s).1 hz
    have hgp := faceMin_pos h𝓕 h𝓕s hy
    have hy' := openStd_subset_closedStd s hy
    have hlt : lo z.1 < hi z.1 :=
      lt_of_le_of_ne (hle z.1 hy') fun h ↦ hgp.ne' ((hdeg z.1 hy').1 h)
    have h := abs_mul_div_lt_of_abs_lt (show 0 < (hi z.1 - lo z.1) / 2 by linarith) hv
    exact ⟨z.1, hy, _, by linarith [abs_lt.1 h], by linarith [abs_lt.1 h], rfl⟩
  · rintro ⟨y, hy, t, h1, h2, rfl⟩
    have hgp := faceMin_pos h𝓕 h𝓕s hy
    have hw : 0 < (hi y - lo y) / 2 := by linarith
    refine ⟨(y, (t - (lo y + hi y) / 2) * faceMin s 𝓕 h𝓕 y / ((hi y - lo y) / 2)),
      (bandModel_inter_lt_iff hs h𝓕 h𝓕s).2 ⟨hy, ?_⟩, ?_⟩
    · simp only
      rw [abs_div, abs_mul, abs_of_pos hw, abs_of_pos hgp, div_lt_iff₀ hw]
      have : |t - (lo y + hi y) / 2| < (hi y - lo y) / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      nlinarith
    · exact bandMap_mk_div hgp.ne' (by linarith)

end Maps

section StdFaces

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- A closed standard simplex lies in the closure of the corresponding open simplex. -/
theorem closedStd_subset_closure_openStd {s : Finset ν} (hs : s.Nonempty) :
    closedStd s ⊆ closure (openStd s) := by
  rw [closedStd_eq_convexHull, openStd_eq_openSimplex]
  exact convexHull_subset_closure_openSimplex (hs.map (f := stdVertex ν))

/-- An inequality of continuous functions on the open simplex extends to the closed one. -/
theorem le_on_closedStd {s : Finset ν} (hs : s.Nonempty) {f g : (ν → ℝ) → ℝ}
    (hf : ContinuousOn f (closedStd s)) (hg : ContinuousOn g (closedStd s))
    (h : ∀ y ∈ openStd s, f y ≤ g y) : ∀ y ∈ closedStd s, f y ≤ g y := fun y hy ↦
  ContinuousWithinAt.closure_le (closedStd_subset_closure_openStd hs hy)
    ((hf y hy).mono (openStd_subset_closedStd s)) ((hg y hy).mono (openStd_subset_closedStd s)) h

/-- The closed standard simplex is monotone in its face. -/
theorem closedStd_mono {s t : Finset ν} (h : t ⊆ s) : closedStd t ⊆ closedStd s :=
  fun _ hy ↦ ⟨hy.1, hy.2.1, fun u hu ↦ hy.2.2 u fun h' ↦ hu (h h')⟩

/-- The support of a point of a closed simplex: the face whose open simplex contains it. -/
theorem mem_openStd_support {s : Finset ν} {y : ν → ℝ} (hy : y ∈ closedStd s) :
    Finset.univ.filter (y · ≠ 0) ⊆ s ∧ (Finset.univ.filter (y · ≠ 0)).Nonempty ∧
      y ∈ openStd (Finset.univ.filter (y · ≠ 0)) := by
  refine ⟨fun u hu ↦ ?_, ?_, fun u hu ↦ ?_, hy.2.1, fun u hu ↦ ?_⟩
  · by_contra h
    exact (Finset.mem_filter.1 hu).2 (hy.2.2 u h)
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    simpa [Finset.sum_eq_zero fun u _ ↦ not_not.1 (h (Finset.mem_univ u))] using hy.2.1
  · exact lt_of_le_of_ne (hy.1 u) (Ne.symm (Finset.mem_filter.1 hu).2)
  · by_contra h
    exact hu (by simp [h])

/-- If `y` lies in the open simplex of `t` and the closed simplex of `s`, then `t ⊆ s`. -/
theorem subset_of_mem_openStd_of_mem_closedStd {s t : Finset ν} {y : ν → ℝ}
    (ht : y ∈ openStd t) (hs : y ∈ closedStd s) : t ⊆ s := fun u hu ↦
  of_not_not fun h ↦ (ht.1 u hu).ne' (hs.2.2 u h)

/-- Open standard simplices of distinct faces are disjoint. -/
theorem eq_of_mem_openStd {s t : Finset ν} {y : ν → ℝ} (hs : y ∈ openStd s)
    (ht : y ∈ openStd t) : s = t :=
  (subset_of_mem_openStd_of_mem_closedStd hs (openStd_subset_closedStd t ht)).antisymm
    (subset_of_mem_openStd_of_mem_closedStd ht (openStd_subset_closedStd s hs))

/-- The closed simplex of a face of `Δ` lies in the realisation `stdSpace Δ`. -/
theorem closedStd_subset_stdSpace {Δ : Set (Finset ν)} {s : Finset ν} (hs : s ∈ Δ) :
    closedStd s ⊆ stdSpace Δ := fun y hy ↦ by
  rw [closedStd_eq_convexHull] at hy
  exact mem_iUnion₂.2 ⟨s, hs, hy⟩

end StdFaces

section Lift

variable {σ ν : Type} [Fintype ν] [DecidableEq ν]

/-- Graph and band conditions at a common height for a strictly increasing family determine the
index and the kind of the cell. -/
theorem eq_and_eq_of_cell_cond {f : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Iio N)) {j j' : ℕ}
    {b b' : Bool} {t : ℝ} (hj : (if b then j + 1 else j) < N)
    (hj' : (if b' then j' + 1 else j') < N)
    (ht : if b then f j < t ∧ t < f (j + 1) else t = f j)
    (ht' : if b' then f j' < t ∧ t < f (j' + 1) else t = f j') : j = j' ∧ b = b' := by
  cases b <;> cases b' <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hj hj' ht ht'
  · exact ⟨hf.injOn hj hj' (ht.symm.trans ht'), rfl⟩
  · have h₁ : j' < j := (hf.lt_iff_lt (show j' < N by omega) hj).1 (ht'.1.trans_eq ht)
    have h₂ : j < j' + 1 := (hf.lt_iff_lt hj hj').1 (ht.symm.trans_lt ht'.2)
    exact absurd h₂ (by omega)
  · have h₁ : j < j' := (hf.lt_iff_lt (show j < N by omega) hj').1 (ht.1.trans_eq ht')
    have h₂ : j' < j + 1 := (hf.lt_iff_lt hj' hj).1 (ht'.symm.trans_lt ht.2)
    exact absurd h₂ (by omega)
  · have h₁ : j < j' + 1 := (hf.lt_iff_lt (show j < N by omega) hj').1 (ht.1.trans ht'.2)
    have h₂ : j' < j + 1 := (hf.lt_iff_lt (show j' < N by omega) hj).1 (ht'.1.trans ht.2)
    exact ⟨by omega, rfl⟩

/-- If a height satisfying a graph or band condition of a strictly increasing family `f` lies
between `f p` and `f q`, then every height satisfying the same condition for another strictly
increasing family `g` lies between `g p` and `g q`. -/
theorem le_and_le_of_cell_cond {f g : ℕ → ℝ} {N : ℕ} (hf : StrictMonoOn f (Iio N))
    (hg : StrictMonoOn g (Iio N)) {p q l : ℕ} {b : Bool} (hp : p < N) (hq : q < N)
    (hl : (if b then l + 1 else l) < N) {τ τ' : ℝ} (h₁ : f p ≤ τ) (h₂ : τ ≤ f q)
    (hτ : if b then f l < τ ∧ τ < f (l + 1) else τ = f l)
    (hτ' : if b then g l < τ' ∧ τ' < g (l + 1) else τ' = g l) : g p ≤ τ' ∧ τ' ≤ g q := by
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hl hτ hτ'
  · subst hτ hτ'
    exact ⟨(hg.le_iff_le hp hl).2 ((hf.le_iff_le hp hl).1 h₁),
      (hg.le_iff_le hl hq).2 ((hf.le_iff_le hl hq).1 h₂)⟩
  · have hpl : p < l + 1 := (hf.lt_iff_lt hp hl).1 (h₁.trans_lt hτ.2)
    have hlq : l < q := (hf.lt_iff_lt (show l < N by omega) hq).1 (hτ.1.trans_le h₂)
    exact ⟨((hg.le_iff_le hp (show l < N by omega)).2 (by omega)).trans hτ'.1.le,
      hτ'.2.le.trans ((hg.le_iff_le hl hq).2 (by omega))⟩

omit [DecidableEq ν] in
/-- The graph of a continuous function over a nonempty closed simplex, through an injective
continuous `h₀`, is a radial cell whose closure is the graph over the closed simplex. -/
theorem exists_isRadialCell_graphCell {s : Finset ν} (hs : s.Nonempty) {h₀ : (ν → ℝ) → σ → ℝ}
    {ζ : (ν → ℝ) → ℝ} (hh₀ : ContinuousOn h₀ (closedStd s)) (hinj : InjOn h₀ (closedStd s))
    (hζ : ContinuousOn ζ (closedStd s)) :
    ∃ (c : Option σ → ℝ) (r : (Option σ → ℝ) → ℝ → Option σ → ℝ),
      IsRadialCell (graphCell h₀ ζ s) c r ∧
        closure (graphCell h₀ ζ s) = closedBandCell h₀ ζ ζ s := by
  classical
  set θ : (ν → ℝ) → Option σ → ℝ := fun y ↦ optionCons (h₀ y) (ζ y)
  have hθ : ContinuousOn θ (closedStd s) := continuous_optionCons.comp_continuousOn (hh₀.prodMk hζ)
  have hθi : InjOn θ (closedStd s) := fun y hy y' hy' h ↦ hinj hy hy' (optionCons_injective h).1
  obtain ⟨hcl, -, hr⟩ := (isRadialModel_closedStd hs).isRadialCell (isCompact_closedStd s)
    (continuous_stdGauge hs).continuousOn hθ hθi
  rw [closedStd_inter_lt_one hs] at hcl hr
  refine ⟨_, _, hr, ?_⟩
  change closure (θ '' openStd s) = _
  rw [hcl]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, _, le_rfl, le_rfl, rfl⟩
  · rintro ⟨y, hy, t, h1, h2, rfl⟩
    exact ⟨y, hy, by rw [le_antisymm h2 h1]⟩

open scoped Classical in
/-- Over a simplex `s` of `Δ`, the functions `ζ s j` and `ζ s (j + 1)` agree at a point of the
closed simplex exactly when the point lies on a face of `𝓕`, the faces on which they agree. -/
theorem eq_iff_faceMin_eq_zero_of_cells {Δ : Set (Finset ν)} {h₀ : (ν → ℝ) → σ → ℝ}
    {B : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h₀ B) {n : Finset ν → ℕ}
    {ζ : Finset ν → ℕ → (ν → ℝ) → ℝ}
    (hcont : ∀ s ∈ Δ, ∀ j < n s, ContinuousOn (ζ s j) (closedStd s))
    (hmono : ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ j j', j < j' → j' < n s → ζ s j y < ζ s j' y)
    (hface : ∀ s ∈ Δ, ∀ t ∈ Δ, t ⊆ s → ∀ j < n s, ∃ l < n t,
      EqOn (ζ s j) (ζ t l) (openStd t))
    {s : Finset ν} (hs : s ∈ Δ) {j : ℕ} (hj : j + 1 < n s) {𝓕 : Finset (Finset ν)}
    (h𝓕 : 𝓕.Nonempty) (_h𝓕e : ∅ ∈ 𝓕) (h𝓕s : ∀ F ∈ 𝓕, ¬ s ⊆ F)
    (h𝓕d : 𝓕 = insert ∅ (s.powerset.filter fun F ↦
      F ≠ s ∧ F.Nonempty ∧ EqOn (ζ s j) (ζ s (j + 1)) (openStd F)))
    {y : ν → ℝ} (hy : y ∈ closedStd s) :
    ζ s j y = ζ s (j + 1) y ↔ faceMin s 𝓕 h𝓕 y = 0 := by
  have hs' := hT.nonempty s hs
  constructor
  · intro hLU
    obtain ⟨hts, htne, hyt⟩ := mem_openStd_support hy
    set t := Finset.univ.filter (y · ≠ 0)
    have ht : t ∈ Δ := hT.down_closed s hs t hts htne
    obtain ⟨p, hp, hEp⟩ := hface s hs t ht hts j (by omega)
    obtain ⟨q, hq, hEq⟩ := hface s hs t ht hts (j + 1) hj
    have hsm : StrictMonoOn (ζ t · y) (Iio (n t)) := fun _ ha _ hb hab ↦
      hmono t ht y hyt _ _ hab hb
    have hpq : p = q := hsm.injOn hp hq ((hEp hyt).symm.trans (hLU.trans (hEq hyt)))
    have hts' : t ≠ s := by
      rintro rfl
      exact (hmono t ht y hyt j (j + 1) (by omega) hj).ne hLU
    have htF : t ∈ 𝓕 := by
      rw [h𝓕d]
      exact Finset.mem_insert_of_mem (Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 hts, hts', htne, fun z hz ↦ by rw [hEp hz, hEq hz, hpq]⟩)
    refine le_antisymm ?_ (faceMin_nonneg h𝓕 hy)
    refine (Finset.inf'_le _ htF).trans (le_of_eq ?_)
    refine Finset.sum_eq_zero fun u hu ↦ ?_
    exact of_not_not fun h ↦ (Finset.mem_sdiff.1 hu).2 (by simp [t, h])
  · intro h0
    obtain ⟨F, hF, hFeq⟩ := Finset.exists_mem_eq_inf' h𝓕 fun F ↦ faceDist s F y
    rw [faceMin] at h0
    rw [h0] at hFeq
    rw [h𝓕d] at hF
    rcases Finset.mem_insert.1 hF with rfl | hF'
    · rw [faceDist_empty ⟨hy.2.1, hy.2.2⟩] at hFeq
      norm_num at hFeq
    obtain ⟨hFs, -, hFne, hFeq'⟩ := Finset.mem_filter.1 hF'
    have hFs := Finset.mem_powerset.1 hFs
    have hyF : y ∈ closedStd F := by
      refine ⟨hy.1, hy.2.1, fun u hu ↦ ?_⟩
      by_cases hus : u ∈ s
      · exact (Finset.sum_eq_zero_iff_of_nonneg fun v _ ↦ hy.1 v).1 hFeq.symm u
          (Finset.mem_sdiff.2 ⟨hus, hu⟩)
      · exact hy.2.2 u hus
    have hLF := (hcont s hs j (by omega)).mono (closedStd_mono hFs)
    have hUF := (hcont s hs (j + 1) hj).mono (closedStd_mono hFs)
    exact le_antisymm (le_on_closedStd hFne hLF hUF (fun z hz ↦ (hFeq' hz).le) y hyF)
      (le_on_closedStd hFne hUF hLF (fun z hz ↦ (hFeq' hz).ge) y hyF)

open scoped Classical in
/-- Over a simplex `s` of `Δ`, the band between `ζ s j` and `ζ s (j + 1)` is a radial cell whose
closure is the closed band. -/
theorem exists_isRadialCell_bandCell_of_cells {Δ : Set (Finset ν)} {h₀ : (ν → ℝ) → σ → ℝ}
    {B : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h₀ B) {n : Finset ν → ℕ}
    {ζ : Finset ν → ℕ → (ν → ℝ) → ℝ}
    (hcont : ∀ s ∈ Δ, ∀ j < n s, ContinuousOn (ζ s j) (closedStd s))
    (hmono : ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ j j', j < j' → j' < n s → ζ s j y < ζ s j' y)
    (hface : ∀ s ∈ Δ, ∀ t ∈ Δ, t ⊆ s → ∀ j < n s, ∃ l < n t,
      EqOn (ζ s j) (ζ t l) (openStd t))
    {s : Finset ν} (hs : s ∈ Δ) {j : ℕ} (hj : j + 1 < n s) :
    ∃ (c : Option σ → ℝ) (r : (Option σ → ℝ) → ℝ → Option σ → ℝ),
      IsRadialCell (bandCell h₀ (ζ s j) (ζ s (j + 1)) s) c r ∧
        closure (bandCell h₀ (ζ s j) (ζ s (j + 1)) s) =
          closedBandCell h₀ (ζ s j) (ζ s (j + 1)) s := by
  have hs' := hT.nonempty s hs
  have hLc := hcont s hs j (by omega)
  have hUc := hcont s hs (j + 1) hj
  set 𝓕 : Finset (Finset ν) := insert ∅ (s.powerset.filter fun F ↦
    F ≠ s ∧ F.Nonempty ∧ EqOn (ζ s j) (ζ s (j + 1)) (openStd F)) with h𝓕d
  have h𝓕 : 𝓕.Nonempty := ⟨∅, Finset.mem_insert_self _ _⟩
  have h𝓕e : ∅ ∈ 𝓕 := Finset.mem_insert_self _ _
  have h𝓕s : ∀ F ∈ 𝓕, ¬ s ⊆ F := by
    intro F hF hsF
    rcases Finset.mem_insert.1 hF with rfl | hF
    · exact hs'.ne_empty (Finset.subset_empty.1 hsF)
    · obtain ⟨hFs, hne, -⟩ := Finset.mem_filter.1 hF
      exact hne ((Finset.mem_powerset.1 hFs).antisymm hsF)
  have hle : ∀ y ∈ closedStd s, ζ s j y ≤ ζ s (j + 1) y :=
    le_on_closedStd hs' hLc hUc fun y hy ↦ (hmono s hs y hy j (j + 1) (by omega) hj).le
  have hdeg : ∀ y ∈ closedStd s, ζ s j y = ζ s (j + 1) y ↔ faceMin s 𝓕 h𝓕 y = 0 := fun _ hy ↦
    eq_iff_faceMin_eq_zero_of_cells hT hcont hmono hface hs hj h𝓕 h𝓕e h𝓕s h𝓕d hy
  obtain ⟨hcl, -, hr⟩ := (isRadialModel_bandModel hs' h𝓕 h𝓕e h𝓕s).isRadialCell
    (isCompact_bandModel h𝓕 h𝓕e) (continuous_bandGauge hs' h𝓕).continuousOn
    (continuousOn_bandMap hs' h𝓕 h𝓕e h𝓕s (hT.continuousOn.mono (closedStd_subset_stdSpace hs))
      hLc hUc hle hdeg)
    (injOn_bandMap hs' h𝓕 h𝓕e h𝓕s (hT.injOn.mono (closedStd_subset_stdSpace hs)) hle hdeg)
  rw [bandMap_image_lt hs' h𝓕 h𝓕e h𝓕s hle hdeg] at hcl hr
  rw [bandMap_image hs' h𝓕 h𝓕e h𝓕s hle hdeg] at hcl
  exact ⟨_, _, hr, hcl⟩

/-- **The lifting step of the triangulation theorem.** Let `h₀` be a standard triangulation of
`B` by `Δ` and, over each simplex `s ∈ Δ`, let `ζ s 0 < ζ s 1 < ⋯ < ζ s (n s - 1)` be functions
continuous on the closed simplex, strictly increasing on the open simplex, each restricting on
the open simplex of each face `t` to a function of the family of `t`. Let `S` be a closed union
of graphs and bounded bands of these functions, each graph and band lying in `S` as soon as it
meets it. Then `S` has a standard triangulation compatible with every family of sets each of
which contains or misses each graph and band. -/
theorem exists_isStdTriangulation_of_cells {Δ : Set (Finset ν)} {h₀ : (ν → ℝ) → σ → ℝ}
    {B : Set (σ → ℝ)} (hT : IsStdTriangulation Δ h₀ B) (n : Finset ν → ℕ)
    (ζ : Finset ν → ℕ → (ν → ℝ) → ℝ)
    (hcont : ∀ s ∈ Δ, ∀ j < n s, ContinuousOn (ζ s j) (closedStd s))
    (hmono : ∀ s ∈ Δ, ∀ y ∈ openStd s, ∀ j j', j < j' → j' < n s → ζ s j y < ζ s j' y)
    (hface : ∀ s ∈ Δ, ∀ t ∈ Δ, t ⊆ s → ∀ j < n s, ∃ l < n t,
      EqOn (ζ s j) (ζ t l) (openStd t))
    {S : Set (Option σ → ℝ)} (hSc : IsClosed S)
    (hS : ∀ x ∈ S, ∃ s ∈ Δ, (∃ j < n s, x ∈ graphCell h₀ (ζ s j) s) ∨
      ∃ j, j + 1 < n s ∧ x ∈ bandCell h₀ (ζ s j) (ζ s (j + 1)) s)
    (hSg : ∀ s ∈ Δ, ∀ j < n s, (graphCell h₀ (ζ s j) s ∩ S).Nonempty →
      graphCell h₀ (ζ s j) s ⊆ S)
    (hSb : ∀ s ∈ Δ, ∀ j, j + 1 < n s → (bandCell h₀ (ζ s j) (ζ s (j + 1)) s ∩ S).Nonempty →
      bandCell h₀ (ζ s j) (ζ s (j + 1)) s ⊆ S)
    {ι : Type*} (A : ι → Set (Option σ → ℝ))
    (hAg : ∀ i, ∀ s ∈ Δ, ∀ j < n s,
      graphCell h₀ (ζ s j) s ⊆ A i ∨ Disjoint (graphCell h₀ (ζ s j) s) (A i))
    (hAb : ∀ i, ∀ s ∈ Δ, ∀ j, j + 1 < n s →
      bandCell h₀ (ζ s j) (ζ s (j + 1)) s ⊆ A i ∨
        Disjoint (bandCell h₀ (ζ s j) (ζ s (j + 1)) s) (A i)) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Δ' : Set (Finset κ))
      (h' : (κ → ℝ) → Option σ → ℝ), IsStdTriangulation Δ' h' S ∧
      ∀ i, ∀ c ∈ Δ', h' '' openSimplex (c.map (stdVertex κ)) ⊆ A i ∨
        Disjoint (h' '' openSimplex (c.map (stdVertex κ))) (A i) := by
  classical
  have hsm : ∀ s ∈ Δ, ∀ y ∈ openStd s, StrictMonoOn (ζ s · y) (Iio (n s)) :=
    fun s hs y hy _ _ _ hb hab ↦ hmono s hs y hy _ _ hab hb
  let lo : Finset ν × ℕ × Bool → (ν → ℝ) → ℝ := fun p ↦ ζ p.1 p.2.1
  let hi : Finset ν × ℕ × Bool → (ν → ℝ) → ℝ := fun p ↦
    ζ p.1 (if p.2.2 then p.2.1 + 1 else p.2.1)
  let cell : Finset ν × ℕ × Bool → Set (Option σ → ℝ) := fun p ↦
    if p.2.2 then bandCell h₀ (lo p) (hi p) p.1 else graphCell h₀ (lo p) p.1
  let idx : Finset ν × ℕ × Bool → Prop := fun p ↦
    p.1 ∈ Δ ∧ (if p.2.2 then p.2.1 + 1 else p.2.1) < n p.1
  let valid : Finset ν × ℕ × Bool → Prop := fun p ↦ idx p ∧ cell p ⊆ S
  have hlo_lt : ∀ p, idx p → p.2.1 < n p.1 := fun p hp ↦ by
    have h := hp.2
    split_ifs at h <;> omega
  have hcell_mem : ∀ p x, x ∈ cell p ↔ ∃ y ∈ openStd p.1, ∃ t,
      (if p.2.2 then ζ p.1 p.2.1 y < t ∧ t < ζ p.1 (p.2.1 + 1) y else t = ζ p.1 p.2.1 y) ∧
        optionCons (h₀ y) t = x := by
    rintro ⟨s, j, (_ | _)⟩ x <;> simp [cell, lo, hi, graphCell, bandCell, and_assoc]
  have hrad : ∀ p, idx p → ∃ (c : Option σ → ℝ) (r : (Option σ → ℝ) → ℝ → Option σ → ℝ),
      IsRadialCell (cell p) c r ∧ closure (cell p) = closedBandCell h₀ (lo p) (hi p) p.1 := by
    rintro ⟨s, j, b⟩ hp
    have hs : s ∈ Δ := hp.1
    cases b
    · exact exists_isRadialCell_graphCell (hT.nonempty s hs)
        (hT.continuousOn.mono (closedStd_subset_stdSpace hs))
        (hT.injOn.mono (closedStd_subset_stdSpace hs)) (hcont s hs j (hlo_lt _ hp))
    · exact exists_isRadialCell_bandCell_of_cells hT hcont hmono hface hs (by simpa using hp.2)
  choose! center ray hradial hclosure using hrad
  have hfin : {p | valid p}.Finite := by
    refine (Finset.finite_toSet (Finset.univ ×ˢ
      Finset.range ((Finset.univ : Finset (Finset ν)).sup n + 1) ×ˢ Finset.univ)).subset ?_
    rintro ⟨s, j, b⟩ hp
    have hj := hlo_lt _ hp.1
    have : n s ≤ (Finset.univ : Finset (Finset ν)).sup n := Finset.le_sup (Finset.mem_univ s)
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_range, mem_prod, mem_univ,
      mem_Iio, true_and, and_true]
    simp only at hj
    omega
  let κ := {p // valid p}
  have : Fintype κ := hfin.fintype
  have hScov : ∀ x ∈ S, ∃ a : κ, x ∈ cell a.1 := by
    intro x hx
    obtain ⟨s, hs, ⟨j, hj, hxj⟩ | ⟨j, hj, hxj⟩⟩ := hS x hx
    · have hsub := hSg s hs j hj ⟨x, hxj, hx⟩
      exact ⟨⟨(s, j, false), ⟨hs, by simpa using hj⟩, by simpa [cell] using hsub⟩,
        by simpa [cell] using hxj⟩
    · have hsub := hSb s hs j hj ⟨x, hxj, hx⟩
      exact ⟨⟨(s, j, true), ⟨hs, by simpa using hj⟩, by simpa [cell, lo, hi] using hsub⟩,
        by simpa [cell, lo, hi] using hxj⟩
  have hU : (⋃ a : κ, cell a.1) = S :=
    Subset.antisymm (iUnion_subset fun a ↦ a.2.2) fun x hx ↦ mem_iUnion.2 (hScov x hx)
  by_cases hSe : S = ∅
  · refine ⟨Empty, inferInstance, inferInstance, ∅, fun _ ↦ 0, ⟨fun _ h ↦ h.elim,
      fun _ h ↦ h.elim, ?_, ?_, ?_⟩, fun _ _ h ↦ h.elim⟩ <;> simp [stdSpace, hSe]
  have hκne : Nonempty κ := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hSe
    exact ⟨(hScov x hx).choose⟩
  have hcell_eq : ∀ p q : Finset ν × ℕ × Bool, idx p → idx q → ∀ x, x ∈ cell p → x ∈ cell q →
      p = q := by
    rintro ⟨s, j, b⟩ ⟨s', j', b'⟩ hp hq x hxp hxq
    obtain ⟨y, hy, t, ht, rfl⟩ := (hcell_mem _ x).1 hxp
    obtain ⟨y', hy', t', ht', hx'⟩ := (hcell_mem _ _).1 hxq
    obtain ⟨h1, h2⟩ := optionCons_injective hx'
    have hyy : y' = y := hT.injOn (closedStd_subset_stdSpace hq.1 (openStd_subset_closedStd _ hy'))
      (closedStd_subset_stdSpace hp.1 (openStd_subset_closedStd _ hy)) h1
    subst hyy h2
    obtain rfl := eq_of_mem_openStd hy hy'
    obtain ⟨rfl, rfl⟩ := eq_and_eq_of_cell_cond (hsm s hp.1 y' hy) hp.2 hq.2 ht ht'
    rfl
  have H : IsRadialCellComplex (fun a : κ ↦ cell a.1) (fun a ↦ center a.1) (fun a ↦ ray a.1) := by
    refine ⟨fun a b hab ↦ Set.disjoint_left.2 fun x hxa hxb ↦ hab (Subtype.ext
      (hcell_eq _ _ a.2.1 b.2.1 x hxa hxb)), fun a ↦ hradial a.1 a.2.1, fun a ↦ ?_, ?_⟩
    · exact (closure_minimal a.2.2 hSc).trans hU.ge
    · rintro ⟨⟨s, j, b⟩, hpa⟩ ⟨⟨t, l, b'⟩, hpb⟩ ⟨x, hxb, hxa⟩
      simp only at hxb hxa ⊢
      rw [hclosure _ hpa.1] at hxa ⊢
      have hs : s ∈ Δ := hpa.1.1
      have ht : t ∈ Δ := hpb.1.1
      obtain ⟨y', hy', τ, hτ, rfl⟩ := (hcell_mem _ x).1 hxb
      obtain ⟨y, hy, τ', h1, h2, hx⟩ := hxa
      obtain ⟨hyy, hττ⟩ := optionCons_injective hx
      have hyy' : y = y' := hT.injOn (closedStd_subset_stdSpace hs hy)
        (closedStd_subset_stdSpace ht (openStd_subset_closedStd _ hy')) hyy
      subst hyy' hττ
      have hts : t ⊆ s := subset_of_mem_openStd_of_mem_closedStd hy' hy
      obtain ⟨p, hp, hEp⟩ := hface s hs t ht hts j (hlo_lt _ hpa.1)
      obtain ⟨q, hq, hEq⟩ := hface s hs t ht hts _ hpa.1.2
      intro x'' hx''
      obtain ⟨y'', hy'', τ'', hτ'', rfl⟩ := (hcell_mem _ x'').1 hx''
      obtain ⟨hl, hu⟩ := le_and_le_of_cell_cond (hsm t ht y hy') (hsm t ht y'' hy'') hp hq
        hpb.1.2 ((hEp hy').symm.trans_le h1) (h2.trans_eq (hEq hy')) hτ hτ''
      exact ⟨y'', closedStd_mono hts (openStd_subset_closedStd _ hy''), τ'',
        (hEp hy'').trans_le hl, hu.trans_eq (hEq hy'').symm, rfl⟩
  obtain ⟨hTS, hcompat⟩ := H.isStdTriangulation
  rw [hU] at hTS
  refine ⟨κ, inferInstance, inferInstance, _, _, hTS, fun i c hc ↦ ?_⟩
  obtain ⟨a, -, ha⟩ := hcompat c hc
  obtain ⟨⟨s, j, b⟩, hp⟩ := a
  have hs := hp.1.1
  have hj := hlo_lt _ hp.1
  cases b
  · rcases hAg i s hs j hj with h | h
    · exact Or.inl (ha.trans (by simpa [cell] using h))
    · exact Or.inr (h.mono_left (by simpa [cell] using ha))
  · have hj1 : j + 1 < n s := by simpa [idx] using hp.1.2
    rcases hAb i s hs j hj1 with h | h
    · exact Or.inl (ha.trans (by simpa [cell, lo, hi] using h))
    · exact Or.inr (h.mono_left (by simpa [cell, lo, hi] using ha))

end Lift

end MMP
