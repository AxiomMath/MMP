module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Resolution.Principalization
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupSequence

/-!
# Coordinates, twists and termination in Kollár's order reduction

Five lemmas from Kollár's resolution of singularities, Chapter 3.

* **Common coordinates for two hypersurfaces** (3.95). Let `X` satisfy (ST): a smooth,
  equidimensional scheme of finite type over a field `k` of characteristic zero. Let `p ∈ X` be a
  closed point, `n = dim_p X`, `E = (E¹, …, Eˢ)` an ordered divisor and `H`, `H'` closed
  subschemes through `p` such that `H + ∑ᵢ Eⁱ` and `H' + ∑ᵢ Eⁱ` are snc. If `x₁`, `x₁'`, `eⱼ` are
  local equations of `H`, `H'` and of the `Eⁱ` through `p`, there are `x_l` such that both
  `(x₁, (eⱼ), (x_l))` and `(x₁', (eⱼ), (x_l))` are regular systems of parameters of `𝒪_{X,p}`.
  The proof is linear algebra in `T = 𝔪_p/𝔪_p²`: the snc hypotheses make the classes of
  `(x₁, e)` and of `(x₁', e)` independent; if `x̄₁' ∈ V = ⟨x̄₁, ē⟩` any complement of `V` works,
  otherwise adjoin `x̄₁ + x̄₁'` to a basis of a complement of `⟨x̄₁, x̄₁', ē⟩`. Nakayama's lemma
  lifts the resulting spanning families of length `dim T` to generators of `𝔪_p`.
* **Twisting by divisorial components of the cosupport** (proof of 3.102). For `K ⊆ 𝒪_X` with
  `maxord K ≤ μ`, a smooth divisor `D` and `Z = Z_{-1}(K, μ, D)`, the invertible ideal `I_Z^μ`
  divides `K`, and `K_0 = 𝒪_X(μZ)·K` agrees with `K` off `Z` and is the unit ideal on `Z`. At
  `x ∈ Z` the divisor `D` agrees with `Z` near `x`, so `I_{Z,x} = (t)` is a height-one prime of
  the regular local ring `𝒪_{X,x}` and `K_x ⊆ (t)^μ`; if `(K_0)_x ≠ 𝒪_{X,x}` then
  `K_x ⊆ 𝔪_x^{μ+1}`, contradicting `ord_x K ≤ μ`.
* **The Step-3.`r` blow-up preserves `m_t < m` for `t < r`** (3.111). A `t`-fold weight not
  involving the exceptional divisor `F` is bounded by an old `t`-fold weight; one involving `F`
  over `x ∈ Z ∩ E^I`, `|I| = t - 1`, is at most
  `σ_I(x) + m_r - m ≤ σ_{I ∪ {j}}(x) + σ_{J_* \ {j}}(x) - m < m` for `j ∈ J_* \ I`.
* **Step 3.`r` terminates** (3.111), by well-founded induction on `(m_r, n_r)` in the
  lexicographic order: each blow-up keeps the data monomial, keeps `m_t < m` for `t < r` and
  lowers `(m_r, n_r)` while `m_r ≥ m`.
* **Principalization forces a centre to meet a codimension `≥ 2` component** (p. 137). If no
  centre met the fibre over the generic point `η`, the blow-up sequence would be an isomorphism
  near `η`, so `I` would be principal near `η`, and Krull's principal ideal theorem would give
  `codim ≤ 1`.

## Main results

* `MMP.Resolution.exists_isRegularSystemOfParameters_cons_append_of_isSNCFamily`: common
  coordinates for two hypersurfaces meeting an snc divisor (3.95)
* `MMP.Resolution.isEffectiveCartierDivisor_divisorComponentCentre`: `Z_{-1}(K, μ, D)` is an
  effective Cartier divisor, so its blow-up is an isomorphism
  (`MMP.Resolution.isIso_blowUpToBase_divisorComponentCentre`)
* `MMP.Resolution.pow_mul_idealColon_divisorComponentCentre`
* `MMP.Resolution.MonomialData.maxStratumWeight_step_lt`
* `MMP.Resolution.MonomialData.exists_maxStratumWeight_iterate_lt`
* `MMP.Resolution.ClosedBlowupSequence.entryIndex_lt_length_of_isLocallyPrincipal`

## Implementation notes

(ST) is spelled as in `MMP.Resolution.IsTriple`: `CharZero k`, `MMP.Mori.IsSmoothScheme sX`,
`LocallyOfFiniteType sX`, `QuasiCompact sX`, `Equidimensional X`. The local dimension `dim_p X`
is `topologicalKrullDimAt X p`. The sum `H + ∑ᵢ Eⁱ` is the family
`Option (Fin s) → X.IdealSheafData` sending `none` to `H`; its being snc
(`MMP.Resolution.IsSNCFamily`) contains the smoothness of `H` and of the `Eⁱ`. The components
`Eⁱ` through `p` are enumerated by `ε : Fin r ≃ {i // p ∈ Eⁱ}`.

The twist `𝒪_X(μZ)·K` is the ideal quotient `(K : I_Z^μ)` (`MMP.Resolution.idealColon`), as for
`MMP.Resolution.MarkedIdeal.birationalTransform`; the inclusion `K_0 ⊆ 𝒪_X` is then the
divisibility `I_Z^μ·(K : I_Z^μ) = K`. The components of a closed subset of a locally noetherian
scheme form a locally finite family, so no quasi-compactness is needed there.

The hypothesis `CharZero C.k` on monomial data is the standing convention of Kollár's §3, under
which `MMP.Resolution.MonomialData.step_spec` describes a single blow-up.

For the entry index, the closed subscheme `X ⊆ P` is its ideal sheaf `I`; "`η` is the generic
point of an irreducible component of `X`" is maximality of `closure {η}` among irreducible
subsets of `I.support`, and "`codim ≥ 2`" is a strict chain `closure {η} ⊊ Y₁ ⊊ Y₂` of
irreducible closed subsets, as in `MMP.Resolution.IsAdmissibleEmbedding`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.95, 3.102, 3.111, p. 137]
-/

universe u

namespace MMP.Resolution

/-! ### Common coordinates for two hypersurfaces -/

section CommonCoordinates

open IsLocalRing AlgebraicGeometry Submodule

section Cotangent

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Composition with `g` commutes with `Fin.cons` and `Fin.append`. -/
private lemma comp_cons_append {α β : Type*} (g : α → β) {r m : ℕ} (a : α) (w : Fin r → α)
    (y : Fin m → α) :
    g ∘ Fin.cons a (Fin.append w y) = Fin.cons (g a) (Fin.append (g ∘ w) (g ∘ y)) := by
  rw [Fin.comp_cons]
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Nakayama: elements of `𝔪` generate `𝔪` iff their classes span `𝔪/𝔪²`. -/
private lemma span_range_toCotangent_eq_top_iff [IsNoetherianRing R] {ι : Type*}
    (y : ι → maximalIdeal R) :
    span (ResidueField R) (Set.range ((maximalIdeal R).toCotangent ∘ y)) = ⊤ ↔
      Ideal.span (Set.range (Subtype.val ∘ y)) = maximalIdeal R := by
  rw [Set.range_comp, CotangentSpace.span_image_eq_top_iff,
    ← (map_injective_of_injective (maximalIdeal R).injective_subtype).eq_iff,
    map_span, Submodule.map_top, range_subtype, ← Set.range_comp]
  rfl

/-- If `a ∈ (b)`, the class of `a` in `𝔪/𝔪²` is a multiple of that of `b`. -/
private lemma toCotangent_mem_span_singleton {a b : maximalIdeal R}
    (h : (a : R) ∈ Ideal.span {(b : R)}) :
    (maximalIdeal R).toCotangent a ∈ ResidueField R ∙ (maximalIdeal R).toCotangent b := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [show a = c • b from Subtype.ext hc.symm, map_smul]
  exact smul_of_tower_mem _ c (mem_span_singleton_self _)

/-- A family that is, entry by entry, a nonzero multiple of an injectively reindexed linearly
independent family is linearly independent. -/
private lemma linearIndependent_of_mem_span_singleton {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {ι ι' : Type*} {b : ι' → M} (hb : LinearIndependent K b) {σ : ι → ι'}
    (hσ : Function.Injective σ) {f : ι → M} (hf : ∀ i, f i ∈ K ∙ b (σ i))
    (hf' : ∀ i, b (σ i) ∈ K ∙ f i) : LinearIndependent K f := by
  choose c hc using fun i => mem_span_singleton.1 (hf i)
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h0
    have h := hf' i
    rw [← hc i, h0, zero_smul, span_singleton_eq_bot.2 rfl, mem_bot] at h
    exact hb.ne_zero _ h
  convert (hb.comp σ hσ).units_smul (fun i => Units.mk0 (c i) (hc0 i)) using 1
  funext i
  simp [← hc i]

/-- If the classes of `(a, w, y)` span `𝔪/𝔪²` and `dim R` is the length of the family, then
`(a, w, y)` is a regular system of parameters. -/
private lemma isRegularSystemOfParameters_cons_append [IsNoetherianRing R] {r m : ℕ}
    (hdim : ringKrullDim R = (r + m + 1 : ℕ)) (a : maximalIdeal R) (w : Fin r → maximalIdeal R)
    (y : Fin m → maximalIdeal R)
    (h : span (ResidueField R) (Set.range (Fin.cons ((maximalIdeal R).toCotangent a)
      (Fin.append ((maximalIdeal R).toCotangent ∘ w) ((maximalIdeal R).toCotangent ∘ y)))) = ⊤) :
    MMP.Mori.IsRegularSystemOfParameters
      (Fin.cons (a : R) (Fin.append (Subtype.val ∘ w) (Subtype.val ∘ y))) := by
  rw [← comp_cons_append] at h ⊢
  exact ⟨(span_range_toCotangent_eq_top_iff _).1 h, hdim⟩

variable [IsNoetherianRing R] {N : ℕ} {z : Fin N → R}

/-- The dimension of `𝔪/𝔪²` is the length of a regular system of parameters. -/
private lemma finrank_cotangentSpace_eq (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    Module.finrank (ResidueField R) (CotangentSpace R) = N := by
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
  rw [hz.2] at this
  exact_mod_cast this

/-- An element generating the same ideal as a member of a regular system of parameters lies
in `𝔪`. -/
private lemma mem_maximalIdeal_of_span_eq (hz : MMP.Mori.IsRegularSystemOfParameters z)
    {a : R} {i : Fin N} (h : Ideal.span {a} = Ideal.span {z i}) : a ∈ maximalIdeal R :=
  (Ideal.span_singleton_le_iff_mem _).1
    (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩))

/-- Elements generating the same principal ideals as distinct members of a regular system of
parameters have linearly independent classes in `𝔪/𝔪²`. -/
private lemma linearIndependent_toCotangent (hz : MMP.Mori.IsRegularSystemOfParameters z)
    {ι : Type*} {σ : ι → Fin N} (hσ : Function.Injective σ) (f : ι → maximalIdeal R)
    (hf : ∀ i, Ideal.span {(f i : R)} = Ideal.span {z (σ i)}) :
    LinearIndependent (ResidueField R) ((maximalIdeal R).toCotangent ∘ f) := by
  let zm : Fin N → maximalIdeal R := fun i => ⟨z i, mem_maximalIdeal_of_span_eq hz rfl⟩
  have hspan := (span_range_toCotangent_eq_top_iff zm).2 hz.1
  have hli : LinearIndependent (ResidueField R) ((maximalIdeal R).toCotangent ∘ zm) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by simp [finrank_cotangentSpace_eq hz])
  refine linearIndependent_of_mem_span_singleton hli hσ (fun i => ?_) (fun i => ?_) <;>
    refine toCotangent_mem_span_singleton ?_
  · exact hf i ▸ Ideal.mem_span_singleton_self _
  · exact (hf i).symm ▸ Ideal.mem_span_singleton_self _

end Cotangent

section LinearAlgebra

variable {K T : Type*} [Field K] [AddCommGroup T] [Module K T] [FiniteDimensional K T]

private lemma span_range_cons_append (a : T) {r m : ℕ} (w : Fin r → T) (y : Fin m → T) :
    span K (Set.range (Fin.cons a (Fin.append w y) : Fin (r + m + 1) → T)) =
      K ∙ a ⊔ span K (Set.range w) ⊔ span K (Set.range y) := by
  rw [Fin.range_cons, MMP.Flips.ResolutionInputs.range_append, span_insert, span_union,
    sup_assoc]

private lemma finrank_span_singleton_sup {r : ℕ} {a : T} {w : Fin r → T}
    (h : LinearIndependent K (Fin.cons a w : Fin (r + 1) → T)) :
    Module.finrank K ↥(K ∙ a ⊔ span K (Set.range w)) = r + 1 := by
  rw [← span_insert, ← Fin.range_cons, finrank_span_eq_card h, Fintype.card_fin]

private lemma span_singleton_sup_span_singleton_add (x z : T) :
    K ∙ x ⊔ K ∙ (x + z) = K ∙ x ⊔ K ∙ z := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_) <;>
    rw [span_singleton_le_iff_mem]
  · exact add_mem (mem_sup_left (mem_span_singleton_self x))
      (mem_sup_right (mem_span_singleton_self z))
  · have h : x + z ∈ K ∙ x ⊔ K ∙ (x + z) := mem_sup_right (mem_span_singleton_self _)
    simpa using sub_mem h (mem_sup_left (mem_span_singleton_self x))

/-- The span of the vectors of a basis of a subspace `C`, viewed in the ambient space, is `C`. -/
private lemma span_range_basis_subtype (C : Submodule K T) {m : ℕ} (b : Module.Basis (Fin m) K C) :
    span K (Set.range (fun i => (b i : T))) = C := by
  rw [show (fun i => (b i : T)) = C.subtype ∘ b from rfl, Set.range_comp, ← map_span,
    b.span_eq, Submodule.map_top, range_subtype]

/-- Two hyperplane equations completing the same independent family `w` admit a common
completion to spanning families of length `dim T`. -/
private lemma exists_common_completion {r : ℕ} (a a' : T) (w : Fin r → T)
    (ha : LinearIndependent K (Fin.cons a w : Fin (r + 1) → T))
    (ha' : LinearIndependent K (Fin.cons a' w : Fin (r + 1) → T)) :
    ∃ m : ℕ, r + m + 1 = Module.finrank K T ∧ ∃ y : Fin m → T,
      span K (Set.range (Fin.cons a (Fin.append w y) : Fin (r + m + 1) → T)) = ⊤ ∧
        span K (Set.range (Fin.cons a' (Fin.append w y) : Fin (r + m + 1) → T)) = ⊤ := by
  simp only [span_range_cons_append]
  set W := span K (Set.range w)
  by_cases hmem : a' ∈ K ∙ a ⊔ W
  · -- the two spans agree; any complement of `V = ⟨a, w⟩` works
    have hVV : K ∙ a' ⊔ W = K ∙ a ⊔ W := eq_of_le_of_finrank_eq
      (sup_le ((span_singleton_le_iff_mem _ _).2 hmem) le_sup_right)
      (by rw [finrank_span_singleton_sup ha, finrank_span_singleton_sup ha'])
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (K ∙ a ⊔ W)
    have := finrank_add_eq_of_isCompl hC
    rw [finrank_span_singleton_sup ha] at this
    refine ⟨Module.finrank K C, by omega, fun i => (Module.finBasis K C i : T), ?_⟩
    simp [span_range_basis_subtype, hVV, hC.sup_eq_top]
  · -- adjoin `a + a'` to a basis of a complement of `U = ⟨a, a', w⟩`
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (K ∙ a ⊔ K ∙ a' ⊔ W)
    have := finrank_add_eq_of_isCompl hC
    rw [sup_comm (K ∙ a), sup_assoc, ← span_insert, ← Fin.range_cons,
      finrank_span_singleton_sup (linearIndependent_fin_cons.2 ⟨ha, by
        rwa [Fin.range_cons, span_insert]⟩)] at this
    refine ⟨Module.finrank K C + 1, by omega,
      Fin.cons (a + a') fun i => (Module.finBasis K C i : T), ?_⟩
    rw [Fin.range_cons, span_insert, span_range_basis_subtype]
    have key (c : T) (hc : K ∙ c ⊔ K ∙ (a + a') = K ∙ a ⊔ K ∙ a') :
        K ∙ c ⊔ W ⊔ (K ∙ (a + a') ⊔ C) = ⊤ := by
      rw [← hC.sup_eq_top, ← hc]; ac_rfl
    exact ⟨key a (span_singleton_sup_span_singleton_add a a'),
      key a' (by rw [add_comm, span_singleton_sup_span_singleton_add, sup_comm])⟩

end LinearAlgebra

/-- At a point `p` of an snc family `G + ∑ Eⁱ`, a local equation `g` of `G` and local equations
`e` of the `Eⁱ` through `p` lie in `𝔪_p` and have linearly independent classes in `𝔪_p/𝔪_p²`. -/
private lemma linearIndependent_toCotangent_of_isSNCFamily {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X]
    {E : MMP.Resolution.OrderedDivisor X} {G : X.IdealSheafData}
    (hG : MMP.Resolution.IsSNCFamily sX (fun o : Option (Fin E.s) => o.elim G E.E))
    {p : X} (hpG : p ∈ (G.support : Set X)) {g : X.presheaf.stalk p}
    (hg : IdealSheafData.stalk G p = Ideal.span {g})
    {r : ℕ} (ε : Fin r ≃ {i // p ∈ ((E.E i).support : Set X)}) {e : Fin r → X.presheaf.stalk p}
    (he : ∀ j, IdealSheafData.stalk (E.E (ε j)) p = Ideal.span {e j}) :
    ∃ (hgm : g ∈ maximalIdeal (X.presheaf.stalk p))
      (hem : ∀ j, e j ∈ maximalIdeal (X.presheaf.stalk p)),
      LinearIndependent (ResidueField (X.presheaf.stalk p))
        ((maximalIdeal (X.presheaf.stalk p)).toCotangent ∘
          Fin.cons ⟨g, hgm⟩ (fun j => ⟨e j, hem j⟩) : Fin (r + 1) → _) := by
  obtain ⟨N, z, c, hz, hc, hcinj⟩ := hG.2 p
  let iE (j : Fin r) : {o : Option (Fin E.s) // p ∈ (o.elim G E.E).support} :=
    ⟨some (ε j).1, (ε j).2⟩
  have hgz : Ideal.span {g} = Ideal.span {z (c ⟨none, hpG⟩)} := hg.symm.trans (hc ⟨none, hpG⟩)
  have hez (j : Fin r) : Ideal.span {e j} = Ideal.span {z (c (iE j))} :=
    (he j).symm.trans (hc (iE j))
  refine ⟨mem_maximalIdeal_of_span_eq hz hgz, fun j => mem_maximalIdeal_of_span_eq hz (hez j),
    linearIndependent_toCotangent hz (σ := Fin.cons (c ⟨none, hpG⟩) (c ∘ iE)) ?_ _
      (Fin.cases hgz hez)⟩
  refine Fin.cons_injective_iff.2 ⟨fun ⟨j, hj⟩ => ?_, hcinj.comp fun j j' h => ?_⟩
  · simpa [iE] using congrArg Subtype.val (hcinj hj)
  · exact ε.injective (Subtype.ext (by simpa [iE, Subtype.ext_iff] using h))

/-- **Common coordinates for two hypersurfaces** (Kollár 3.95). Let `X` satisfy (ST), `p` a
closed point and `n = dim_p X`. If `H + ∑ᵢ Eⁱ` and
`H' + ∑ᵢ Eⁱ` are snc, `p ∈ H ∩ H'`, and `x₁`, `x₁'`, `e j` generate the ideals of `H`, `H'`,
`E^{ε j}` in `𝒪_{X,p}`, then there are `x : Fin m → 𝒪_{X,p}`, `r + m + 1 = n`, such that both
`(x₁, e, x)` and `(x₁', e, x)` are regular systems of parameters of `𝒪_{X,p}`. -/
@[mmp "lem_kr3d_common_coordinates_for_two_hypersurfaces"]
public theorem exists_isRegularSystemOfParameters_cons_append_of_isSNCFamily
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hXeq : TopologicalSpace.Equidimensional X) (E : OrderedDivisor X) (H H' : X.IdealSheafData)
    (hH : IsSNCFamily sX (fun o : Option (Fin E.s) => o.elim H E.E))
    (hH' : IsSNCFamily sX (fun o : Option (Fin E.s) => o.elim H' E.E))
    (p : X) (hp : IsClosed ({p} : Set X)) {n : ℕ} (hn : topologicalKrullDimAt X p = n)
    (hpH : p ∈ (H.support : Set X)) (hpH' : p ∈ (H'.support : Set X))
    (x₁ x₁' : X.presheaf.stalk p)
    (hx₁ : AlgebraicGeometry.IdealSheafData.stalk H p = Ideal.span {x₁})
    (hx₁' : AlgebraicGeometry.IdealSheafData.stalk H' p = Ideal.span {x₁'})
    {r : ℕ} (ε : Fin r ≃ {i // p ∈ ((E.E i).support : Set X)}) (e : Fin r → X.presheaf.stalk p)
    (he : ∀ j, AlgebraicGeometry.IdealSheafData.stalk (E.E (ε j)) p = Ideal.span {e j}) :
    ∃ m : ℕ, r + m + 1 = n ∧ ∃ x : Fin m → X.presheaf.stalk p,
      MMP.Mori.IsRegularSystemOfParameters (Fin.cons x₁ (Fin.append e x)) ∧
        MMP.Mori.IsRegularSystemOfParameters (Fin.cons x₁' (Fin.append e x)) := by
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  have hdim : ringKrullDim (X.presheaf.stalk p) = n := by
    rw [← hn, topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX p hp]
  obtain ⟨N, z, -, hz, -⟩ := hH.2 p
  have hfin : Module.finrank (ResidueField (X.presheaf.stalk p))
      (CotangentSpace (X.presheaf.stalk p)) = n := by
    rw [finrank_cotangentSpace_eq hz]
    exact_mod_cast hz.2.symm.trans hdim
  obtain ⟨hx₁m, hem, hli⟩ := linearIndependent_toCotangent_of_isSNCFamily hH hpH hx₁ ε he
  obtain ⟨hx₁m', _, hli'⟩ := linearIndependent_toCotangent_of_isSNCFamily hH' hpH' hx₁' ε he
  rw [Fin.comp_cons] at hli hli'
  obtain ⟨m, hm, y, hy, hy'⟩ := exists_common_completion _ _ _ hli hli'
  choose ym hym using fun j => (maximalIdeal (X.presheaf.stalk p)).toCotangent_surjective (y j)
  have hym' : (maximalIdeal (X.presheaf.stalk p)).toCotangent ∘ ym = y := funext hym
  have hdim' : ringKrullDim (X.presheaf.stalk p) = ((r + m + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim, hm, hfin]
  rw [← hym'] at hy hy'
  exact ⟨m, hm.trans hfin, Subtype.val ∘ ym,
    isRegularSystemOfParameters_cons_append hdim' ⟨x₁, hx₁m⟩ (fun j => ⟨e j, hem j⟩) ym hy,
    isRegularSystemOfParameters_cons_append hdim' ⟨x₁', hx₁m'⟩ (fun j => ⟨e j, hem j⟩) ym hy'⟩

end CommonCoordinates

/-! ### Twisting by the divisorial components of the cosupport -/

section DivisorComponentTwist

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- An irreducible subset `W` of `D` is irreducible as a subset of the subspace `D`. -/
private theorem isIrreducible_preimage_val {D W : Set T} (hW : IsIrreducible W) (hWD : W ⊆ D) :
    IsIrreducible ((Subtype.val : D → T) ⁻¹' W) := by
  obtain ⟨⟨a, ha⟩, hpre⟩ := hW
  refine ⟨⟨⟨a, hWD ha⟩, ha⟩, ?_⟩
  rintro u v hu hv ⟨p, hpW, hpu⟩ ⟨q, hqW, hqv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨z, hzW, hzu, hzv⟩ := hpre u' v' hu' hv' ⟨p, hpW, hpu⟩ ⟨q, hqW, hqv⟩
  exact ⟨⟨z, hWD hzW⟩, hzW, hzu, hzv⟩

/-- A component of `D ⊆ T` is an irreducible component of the subspace `D`. -/
private theorem preimage_val_mem_irreducibleComponents {D W : Set T} (hW : W ∈ componentsOf D) :
    (Subtype.val : D → T) ⁻¹' W ∈ irreducibleComponents D := by
  refine ⟨isIrreducible_preimage_val hW.1.1 hW.1.2, fun C hC hle => ?_⟩
  have hsub : W ⊆ Subtype.val '' C := fun w hw => ⟨⟨w, hW.1.2 hw⟩, hle hw, rfl⟩
  have h2 := hW.2 ⟨hC.image _ continuous_subtype_val.continuousOn,
    by rintro _ ⟨c, -, rfl⟩; exact c.2⟩ hsub
  exact fun c hc => h2 ⟨c, hc, rfl⟩

end Topology

/-- The components of a closed subset of a locally noetherian scheme form a locally finite
family. -/
private theorem locallyFinite_componentsOf {X : Scheme} [IsLocallyNoetherian X] {D : Set X}
    (hD : IsClosed D) : LocallyFinite fun W : componentsOf D => (W : Set X) := by
  have h := locallyFinite_image_irreducibleComponents_of_isLocallyNoetherianSpace
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) (Subtype.val : D → X)
    hD.isClosedEmbedding_subtypeVal
  let g : componentsOf D → irreducibleComponents D :=
    fun W => ⟨_, preimage_val_mem_irreducibleComponents W.2⟩
  have hg : ∀ W, Subtype.val '' (g W : Set D) = W := fun W => by
    simp only [g, Subtype.image_preimage_coe]
    exact Set.inter_eq_right.mpr W.2.1.2
  have hinj : Function.Injective g := fun W W' hWW' => Subtype.ext (by rw [← hg W, ← hg W', hWW'])
  convert h.comp_injective hinj using 1
  exact funext fun W => (hg W).symm

/-- Any union of components of a closed subset of a locally noetherian scheme is closed. -/
private theorem isClosed_sUnion_of_subset_componentsOf {X : Scheme} [IsLocallyNoetherian X]
    {D : Set X} (hD : IsClosed D) {S : Set (Set X)} (hS : S ⊆ componentsOf D) :
    IsClosed (⋃₀ S) := by
  let g : S → componentsOf D := fun W => ⟨W.1, hS W.2⟩
  have hg : Function.Injective g := fun W W' h => Subtype.ext (congrArg Subtype.val h :)
  have hlf : LocallyFinite fun W : S => (W : Set X) :=
    (locallyFinite_componentsOf hD).comp_injective hg
  rw [Set.sUnion_eq_iUnion]
  exact hlf.isClosed_iUnion fun W => Aux.isClosed_of_mem_componentsOf hD (hS W.2)

/-- On a smooth scheme over a field, a smooth closed subscheme `D` of pure codimension one is
cut out at each of its points by a single non-zero-divisor. -/
public theorem exists_isRegular_stalk_eq_span {k : Type u} [Field k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    (D : X.IdealSheafData) (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hD' : MMP.Mori.IsPureCodimOne D.support) {x : X} (hx : x ∈ (D.support : Set X)) :
    ∃ t, _root_.IsRegular t ∧ IdealSheafData.stalk D x = Ideal.span {t} := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := Aux.smooth_of_isSmoothScheme' sX hX
  haveI := Aux.smooth_of_isSmoothScheme' (D.subschemeι ≫ sX) hD
  obtain ⟨y, rfl⟩ : x ∈ Set.range D.subschemeι := by rw [D.range_subschemeι]; exact hx
  haveI hR : IsRegularLocalRing (X.presheaf.stalk (D.subschemeι y)) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX _
  haveI : IsRegularLocalRing (D.subscheme.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth_over_field (D.subschemeι ≫ sX) y
  set J := IdealSheafData.stalk D (D.subschemeι y)
  have hJ : IsRegularLocalRing (X.presheaf.stalk (D.subschemeι y) ⧸ J) := by
    let f := (D.subschemeι.stalkMap y).hom
    let e := f.quotientKerEquivOfSurjective (D.subschemeι.stalkMap_surjective y)
    have h1 := IsRegularLocalRing.of_ringEquiv (R := D.subscheme.presheaf.stalk y) e.symm
    rwa [Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk D y] at h1
  haveI hprime : J.IsPrime := by
    haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk (D.subschemeι y) ⧸ J)
    exact Ideal.Quotient.isDomain_iff_prime J |>.1 inferInstance
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk (D.subschemeι y))
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk (D.subschemeι y))
  have hht : J.height = 1 := MMP.Flips.ResolutionInputs.height_stalk_eq_one_of_isPureCodimOne D hD'
  obtain ⟨t, ht⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hht).principal
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hht (by simp [ht])
  exact ⟨t, IsRegular.of_ne_zero ht0, ht⟩

/-- In a local ring, if `I ⊆ 𝔪` and `ord(I^μ·J) ≤ μ`, then `J` is the unit ideal: otherwise
`I^μ·J ⊆ 𝔪^{μ+1}`. -/
private theorem eq_top_of_idealOrder_pow_mul_le {R : Type*} [CommRing R] [IsLocalRing R]
    {I J : Ideal R} {μ : ℕ} (hI : I ≤ maximalIdeal R) (hord : idealOrder (I ^ μ * J) ≤ μ) :
    J = ⊤ := by
  by_contra hne
  have h : I ^ μ * J ≤ maximalIdeal R ^ (μ + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mono (Ideal.pow_right_mono hI μ) (le_maximalIdeal hne)
  have := (le_iSup₂_of_le (μ + 1) h le_rfl : ((μ + 1 : ℕ) : ℕ∞) ≤ idealOrder (I ^ μ * J)).trans
    hord
  norm_cast at this
  omega

/-- Let `S` be a set of components of a smooth divisor `D`, and `Z` the reduced ideal of their
union. At a point `x` of a component `W ∈ S`, the ideal of `Z` agrees with that of `D`: the
components of `D` are disjoint, so near `x` the union of `S` is all of `D`. -/
private theorem stalk_vanishingIdeal_sUnion_eq {k : Type u} [Field k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) {S : Set (Set X)}
    (hS : S ⊆ componentsOf (D.support : Set X)) {W : Set X} (hWS : W ∈ S) {x : X} (hxW : x ∈ W) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (⋃₀ S))) x =
      IdealSheafData.stalk D x := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := Aux.isReduced_subscheme_of_isSmoothScheme sX D hD
  have hDcl : IsClosed (D.support : Set X) := D.support.isClosed
  have hU : IsClosed (⋃₀ S) := isClosed_sUnion_of_subset_componentsOf hDcl hS
  set R : Set X := ⋃₀ (componentsOf (D.support : Set X) \ S)
  have hR : IsClosed R := isClosed_sUnion_of_subset_componentsOf hDcl Set.diff_subset
  have hxR : x ∉ R := by
    rintro ⟨W', hW', hxW'⟩
    exact hW'.2 (Aux.eq_of_mem_componentsOf_of_isSmoothScheme sX D hD hW'.1 (hS hWS) hxW' hxW ▸
      hWS)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D D.support rfl]
  refine IdealSheafData.stalk_vanishingIdeal_congr (V := ⟨Rᶜ, hR.isOpen_compl⟩) hxR ?_
  ext z
  simp only [Closeds.coe_closure, hU.closure_eq, Set.mem_inter_iff, Opens.coe_mk,
    Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨W', hW', hzW'⟩, hzR⟩
    exact ⟨(hS hW').1.2 hzW', hzR⟩
  · rintro ⟨hzD, hzR⟩
    obtain ⟨W', hW', hzW'⟩ := exists_mem_componentsOf hzD
    by_cases h : W' ∈ S
    · exact ⟨⟨W', h, hzW'⟩, hzR⟩
    · exact absurd ⟨W', ⟨hW', h⟩, hzW'⟩ hzR

/-- At each point `x`, the ideal of `Z_{-1}(K, D)` in `𝒪_{X,x}` is generated by a single
non-zero-divisor: a local equation of `D` if `x ∈ Z_{-1}(K, D)`, and `1` otherwise. -/
private theorem exists_isRegular_stalk_divisorComponentCentre {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) (hD' : MMP.Mori.IsPureCodimOne D.support)
    (x : X) : ∃ t, _root_.IsRegular t ∧
      IdealSheafData.stalk (divisorComponentCentre K D) x = Ideal.span {t} := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set S : Set (Set X) := {W | W ∈ componentsOf (D.support : Set X) ∧ W ⊆ K.cosupport}
  have hS : S ⊆ componentsOf (D.support : Set X) := fun W hW => hW.1
  have hU : IsClosed (⋃₀ S) := isClosed_sUnion_of_subset_componentsOf D.support.isClosed hS
  change ∃ t, _ ∧ IdealSheafData.stalk
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (⋃₀ S))) x = _
  by_cases hx : x ∈ ⋃₀ S
  · obtain ⟨W, hWS, hxW⟩ := hx
    obtain ⟨t, ht, htD⟩ := exists_isRegular_stalk_eq_span sX hX D hD hD' ((hS hWS).1.2 hxW)
    exact ⟨t, ht, by rw [stalk_vanishingIdeal_sUnion_eq sX D hD hS hWS hxW, htD]⟩
  · refine ⟨1, isRegular_one, ?_⟩
    rw [Ideal.span_singleton_one, IdealSheafData.stalk_eq_top_iff_notMem_support,
      ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simpa [hU.closure_eq] using hx

/-- On a smooth scheme over a field, for a smooth divisor `D` of pure codimension one, the
centre `Z_{-1}(K, D)` is an effective Cartier divisor. -/
public theorem isEffectiveCartierDivisor_divisorComponentCentre {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hD' : MMP.Mori.IsPureCodimOne D.support) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorComponentCentre K D) :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x _ =>
    exists_isRegular_stalk_divisorComponentCentre sX hX K D hD hD' x

/-- On a smooth scheme over a field, for a smooth divisor `D` of pure codimension one, the
blow-up of `Z_{-1}(K, D)` is an isomorphism. -/
public theorem isIso_blowUpToBase_divisorComponentCentre {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hD' : MMP.Mori.IsPureCodimOne D.support) :
    IsIso (blowUpToBase (divisorComponentCentre K D)) :=
  Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_divisorComponentCentre sX hX K D hD hD')

/-- Let `X` be smooth over a field, `μ ≥ 1`, `K` an ideal sheaf with `maxord K ≤ μ`, `D` a
smooth divisor and `Z = Z_{-1}(K, μ, D)`. Then `I_Z^μ` divides `K`, i.e. `K_0 = (K : I_Z^μ)`
satisfies `I_Z^μ·K_0 = K`; the stalk of `K_0` at `x ∉ Z` is that of `K`, and at `x ∈ Z` it is
`𝒪_{X,x}`. -/
@[mmp "lem_kr3e_divisor_component_twist"]
public theorem pow_mul_idealColon_divisorComponentCentre {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    (K : X.IdealSheafData) (μ : ℕ) (hmu : 1 ≤ μ) (hK : maxOrder K ≤ μ) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) (hD' : MMP.Mori.IsPureCodimOne D.support) :
    let Z := divisorComponentCentre ⟨K, μ⟩ D
    Z ^ μ * idealColon K (Z ^ μ) = K ∧
      (∀ x : X, x ∉ (Z.support : Set X) →
        IdealSheafData.stalk (idealColon K (Z ^ μ)) x = IdealSheafData.stalk K x) ∧
      (∀ x : X, x ∈ (Z.support : Set X) → IdealSheafData.stalk (idealColon K (Z ^ μ)) x = ⊤) := by
  intro Z
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set S : Set (Set X) := {W | W ∈ componentsOf (D.support : Set X) ∧
    W ⊆ (⟨K, μ⟩ : MarkedIdeal X).cosupport}
  have hS : S ⊆ componentsOf (D.support : Set X) := fun W hW => hW.1
  have hZx : ∀ x, ∃ t, _root_.IsRegular t ∧ IdealSheafData.stalk Z x = Ideal.span {t} :=
    exists_isRegular_stalk_divisorComponentCentre sX hX _ D hD hD'
  have hZeq : Z = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (⋃₀ S)) := rfl
  clear_value Z
  have hU : IsClosed (⋃₀ S) := isClosed_sUnion_of_subset_componentsOf D.support.isClosed hS
  have hZsupp : (Z.support : Set X) = ⋃₀ S := by
    rw [hZeq]; simp [hU.closure_eq]
  have hnot : ∀ x ∉ (Z.support : Set X), IdealSheafData.stalk Z x = ⊤ := fun x hx =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx
  -- `I_Z^μ` is invertible and contains `K`
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor (Z ^ μ) := by
    refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x _ => ?_
    obtain ⟨t, ht, htZ⟩ := hZx x
    exact ⟨t ^ μ, ht.pow μ, by rw [IdealSheafData.stalk_pow, htZ, Ideal.span_singleton_pow]⟩
  have hle : K ≤ Z ^ μ := by
    refine IdealSheafData.le_of_stalk_le _ _ fun x => ?_
    rw [IdealSheafData.stalk_pow]
    by_cases hx : x ∈ (Z.support : Set X)
    · obtain ⟨W, hWS, hxW⟩ : x ∈ ⋃₀ S := hZsupp ▸ hx
      obtain ⟨W', hW', -, huniq, -, hord⟩ :=
        exists_component_through sX hX D hD K x ((hS hWS).1.2 hxW)
      obtain rfl := huniq W (hS hWS) hxW
      rw [hZeq, stalk_vanishingIdeal_sUnion_eq sX D hD hS hWS hxW]
      refine hord μ (hWS.2 ?_)
      have hgen := hW'.1.1.isGenericPoint_genericPoint_closure
      rw [(Aux.isClosed_of_mem_componentsOf D.support.isClosed hW').closure_eq] at hgen
      exact hgen.mem
    · rw [hnot x hx, Ideal.top_pow]
      exact le_top
  have hmul : Z ^ μ * idealColon K (Z ^ μ) = K := by
    have hfg := AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor _ hZc
    have hcol : idealColon K (Z ^ μ) = Scheme.IdealSheafData.colon K (Z ^ μ) hfg := by
      unfold idealColon
      exact Scheme.IdealSheafData.ofIdeals_ideal (Scheme.IdealSheafData.colon K (Z ^ μ) hfg)
    rw [hcol]
    exact AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _ hZc hle
  have hst : ∀ x, IdealSheafData.stalk Z x ^ μ * IdealSheafData.stalk (idealColon K (Z ^ μ)) x =
      IdealSheafData.stalk K x := fun x => by
    rw [← IdealSheafData.stalk_pow, ← IdealSheafData.stalk_mul, hmul]
  refine ⟨hmul, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← hst x, hnot x hx, Ideal.top_pow, Ideal.top_mul]
  · refine eq_top_of_idealOrder_pow_mul_le (μ := μ)
      (le_maximalIdeal fun h => (IdealSheafData.stalk_eq_top_iff_notMem_support Z x).1 h hx) ?_
    rw [hst x]
    exact (le_iSup₂_of_le x (Set.mem_univ x) le_rfl : multAt K x ≤ maxOrder K).trans hK

end DivisorComponentTwist

/-! ### The Step-3.`r` blow-ups of monomial data -/

section MonomialStep

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- A coefficient `a_j(x)` is at most the sum of all coefficients of `A`. -/
private theorem coeffAt_le_finsum {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) (j : Fin C.E.s) (x : X) :
    C.coeffAt j x ≤ ∑ᶠ D, C.A D := by
  classical
  unfold MonomialData.coeffAt
  refine finsum_le_finsum' (hfin.subset fun D hD => ?_) hfin fun D => ?_
  · by_contra h
    exact hD (by simp [Function.notMem_support.1 h])
  · dsimp only
    split_ifs <;> simp

/-- A family bounded pointwise by `B` has bounded range. -/
private theorem bddAbove_range_of_le {ι : Sort*} {f : ι → ℕ} {B : ℕ} (h : ∀ i, f i ≤ B) :
    BddAbove (Set.range f) :=
  ⟨B, Set.forall_mem_range.2 h⟩

/-- Every weight `σ_J(x)`, `|J| = r`, is at most `m_r(E, A)`. -/
private theorem stratumWeight_le_maxStratumWeight {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) {r : ℕ} {J : Finset (Fin C.E.s)} (hJ : J.card = r)
    {x : X} (hx : x ∈ C.stratum J) : C.stratumWeight J x ≤ C.maxStratumWeight r := by
  -- every weight `σ_{J'}`, `|J'| = r`, is bounded by `r · ∑ a_D`, so all four suprema are bounded
  have hB : ∀ J' : Finset (Fin C.E.s), J'.card = r → ∀ x',
      C.stratumWeight J' x' ≤ r * ∑ᶠ D, C.A D := fun J' hJ' x' => by
    unfold MonomialData.stratumWeight
    rw [← hJ', ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j _ => coeffAt_le_finsum C hfin j x'
  unfold MonomialData.maxStratumWeight
  exact le_ciSup_of_le (bddAbove_range_of_le fun J' => ciSup_le' fun hJ' => ciSup_le' fun x' =>
      ciSup_le' fun _ => hB J' hJ' x') J <|
    le_ciSup_of_le (bddAbove_range_of_le fun hJ' => ciSup_le' fun x' => ciSup_le' fun _ =>
      hB J hJ' x') hJ <|
    le_ciSup_of_le (bddAbove_range_of_le fun x' => ciSup_le' fun _ => hB J hJ x') x <|
    le_ciSup_of_le (bddAbove_range_of_le fun _ => hB J hJ x) hx le_rfl

/-- The birational transform `π⁻¹_*E^i` lies over `E^i`. -/
private theorem mem_support_of_mem_support_step {X : Scheme.{u}} (C : MonomialData X)
    (m r : ℕ) (i : Fin C.E.s) {x : blowUp (C.stepCenter r)}
    (hx : x ∈ ((C.step m r).E.E (Fin.castSucc i)).support) :
    blowUpToBase (C.stepCenter r) x ∈ (C.E.E i).support := by
  replace hx : x ∈ (((C.step m r).E.E (Fin.castSucc i)).support : Set _) := hx
  simp only [MonomialData.step, OrderedDivisor.totalTransform, Fin.snoc_castSucc,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure] at hx
  exact closure_minimal (Set.preimage_mono Set.diff_subset)
    ((C.E.E i).support.isClosed.preimage (blowUpToBase (C.stepCenter r)).continuous) hx

/-- The coefficient in `A'` of the component of `π⁻¹_*E^i` through
`x'` is at most the coefficient in `A` of the component of `E^i` through `π(x')`. (Both members
are smooth, so at most one component passes through a point; the transform of a component `D`
has coefficient `a_D` or `a_D - m` by `step_spec`.) -/
private theorem coeffAt_step_castSucc_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (i : Fin C.E.s) (x : blowUp (C.stepCenter r)) :
    (C.step m r).coeffAt (Fin.castSucc i) x ≤ C.coeffAt i (blowUpToBase (C.stepCenter r) x) := by
  classical
  obtain ⟨-, -, -, hmd, h5, -, h7⟩ :=
    MMP.Resolution.MonomialData.step_spec C hC hk (by omega : 1 ≤ r) hm hmr
  obtain ⟨-, hlft', -, hsnc', -⟩ := hmd
  haveI : LocallyOfFiniteType (C.step m r).sX := hlft'
  set π := blowUpToBase (C.stepCenter r)
  set E' := (C.step m r).E.E (Fin.castSucc i)
  have hsm := (hsnc'.2.1 (Fin.castSucc i)).2.2
  unfold MonomialData.coeffAt
  by_cases hex : ∃ D : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)),
      D.support ∈ componentsOf (E'.support : Set _) ∧ x ∈ D.support
  swap
  · simp only [not_exists, not_and] at hex
    rw [finsum_eq_zero_of_forall_eq_zero fun D => if_neg fun h => hex D h.1 h.2]
    exact Nat.zero_le _
  obtain ⟨D₀, hD₀c, hxD₀⟩ := hex
  rw [finsum_eq_single _ D₀ fun D hD => if_neg fun hDx => hD
    (Aux.PrimeDivisor.eq_of_support_eq (Aux.eq_of_mem_componentsOf_of_isSmoothScheme _ _ hsm
      hDx.1 hD₀c hDx.2 hxD₀))]
  rw [if_pos ⟨hD₀c, hxD₀⟩]
  set η := D₀.genericPoint
  have hηD₀ : η ∈ (D₀.support : Set _) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hηE' : η ∈ (E'.support : Set _) := hD₀c.1.2 hηD₀
  have hη1 : Order.coheight η = 1 := D₀.coheight_genericPoint
  -- `π η ∉ Z`: otherwise `η` lies on both `π⁻¹_*E^i` and `F`, two members of an snc divisor
  -- through a point of codimension one.
  have hyZ : π η ∉ ((C.stepCenter r).support : Set X) := by
    intro hyZ
    have hηF : η ∈ (((C.step m r).E.E (Fin.last C.E.s)).support : Set _) := by
      have h := h7 hr
      change η ∈ (((C.E.totalTransform (C.stepCenter r)).E (Fin.last C.E.s)).support :
        Set (blowUp (C.stepCenter r)))
      rw [h]
      exact hyZ
    obtain ⟨n, z, c, hz, -, hc⟩ := hsnc'.2.2 η
    have hn : (n : WithBot ℕ∞) = 1 := by
      rw [← hz.2, AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hη1]
      rfl
    have hn1 : n = 1 := by exact_mod_cast hn
    subst hn1
    have := hc (a₁ := ⟨Fin.castSucc i, hηE'⟩) (a₂ := ⟨Fin.last C.E.s, hηF⟩)
      (Subsingleton.elim _ _)
    exact (Fin.castSucc_lt_last i).ne (congrArg Subtype.val this)
  -- over `X ∖ Z` the blow-up is an isomorphism, so `π η` has coheight one
  have hy1 : Order.coheight (π η) = 1 := by
    set V : X.Opens := ⟨((C.stepCenter r).support : Set X)ᶜ,
      (C.stepCenter r).support.isClosed.isOpen_compl⟩
    haveI : IsIso (π ∣_ V) := isIso_blowUp_restrict_compl_support (C.stepCenter r)
    let p : (π ⁻¹ᵁ V).toScheme := ⟨η, hyZ⟩
    have e1 : Order.coheight ((π ⁻¹ᵁ V).ι p) = Order.coheight p :=
      Topology.IsOpenEmbedding.coheight_eq _ (π ⁻¹ᵁ V).ι.isOpenEmbedding
    have e2 : Order.coheight ((π ∣_ V) p) = Order.coheight p :=
      Topology.IsOpenEmbedding.coheight_eq _ (π ∣_ V).isOpenEmbedding
    have e3 : Order.coheight (V.ι ((π ∣_ V) p)) = Order.coheight ((π ∣_ V) p) :=
      Topology.IsOpenEmbedding.coheight_eq _ V.ι.isOpenEmbedding
    have h : V.ι ((π ∣_ V) p) = π η := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      rfl
    have h' : (π ⁻¹ᵁ V).ι p = η := rfl
    rw [← h, e3, e2, ← e1, h', hη1]
  set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π η) hy1
  have hDη : D.genericPoint = π η := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy1
  have hDs : (D.support : Set X) = closure {π η} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hDη]
  have hyE : π η ∈ ((C.E.E i).support : Set X) := mem_support_of_mem_support_step C m r i hηE'
  -- `D` is a component of `E^i`
  have hDc : (D.support : Set X) ∈ componentsOf ((C.E.E i).support : Set X) := by
    rw [hDs]
    refine ⟨⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hyE) (C.E.E i).support.isClosed⟩, ?_⟩
    rintro W ⟨hWi, hWE⟩ hyW
    have hWc : IsIrreducible (closure W) := hWi.closure
    have hWE' : closure W ⊆ ((C.E.E i).support : Set X) :=
      closure_minimal hWE (C.E.E i).support.isClosed
    set w := hWc.genericPoint
    have hw : IsGenericPoint w (closure W) := by
      have := hWc.isGenericPoint_genericPoint_closure
      rwa [closure_closure] at this
    have hyw : w ⤳ π η := hw.specializes (subset_closure (hyW (subset_closure rfl)))
    suffices hwy : w = π η by
      refine subset_closure.trans ?_
      rw [← hw.def, hwy]
    by_contra hne
    have hlt : π η < w := lt_of_le_not_ge hyw fun h => hne (hyw.antisymm h).eq
    have hw0 : Order.coheight w = 0 := by
      have hle : Order.coheight w ≤ 1 := hy1 ▸ Order.coheight_anti hlt.le
      have := Order.coheight_strictAnti hlt (hle.trans_lt (by decide))
      rw [hy1] at this
      exact ENat.lt_one_iff_eq_zero.1 this
    have hmax : IsMax w := Order.coheight_eq_zero.1 hw0
    -- `closure {w}` is an irreducible component of `E^i` of codimension `0`
    have hpure := (hC.2.2.2.1.2.1 i).2.1
    have hcod := hpure (IrreducibleCloseds.closureSingleton w) ⟨?_, ?_⟩
    · rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton w =
        (irreducibleSetEquivPoints (α := X)).symm w from rfl, Order.coheight_orderIso,
        hw0] at hcod
      exact zero_ne_one hcod
    · change closure {w} ⊆ _
      rw [hw.def]
      exact hWE'
    · intro T hT hwT
      have hTi : IsIrreducible (T : Set X) := T.isIrreducible
      have ht : IsGenericPoint hTi.genericPoint (T : Set X) := by
        have := hTi.isGenericPoint_genericPoint_closure
        rwa [T.isClosed.closure_eq] at this
      have hwT' : w ∈ (T : Set X) := hwT (subset_closure rfl)
      have htw : hTi.genericPoint ⤳ w := ht.specializes hwT'
      have hle : hTi.genericPoint ≤ w := hmax htw
      change (T : Set X) ⊆ closure {w}
      rw [← ht.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hle))
        isClosed_closure
  -- `π x ∈ D`
  have hxD : π x ∈ (D.support : Set X) := by
    rw [hDs]
    have hsp : η ⤳ x := Aux.genericPoint_specializes_of_mem_support D₀ hxD₀
    exact specializes_iff_mem_closure.1 (hsp.map π.continuous)
  have hA : (C.step m r).A D₀ ≤ C.A D := by
    rw [h5 D D₀ hDη.symm]
    split_ifs <;> omega
  refine hA.trans ?_
  have hfin : (Function.support C.A).Finite := hC.2.2.2.2.1
  refine le_trans ?_ (single_le_finsum D (hfin.subset ?_) ?_)
  · rw [if_pos ⟨hDc, hxD⟩]
  · intro D' hD'
    by_contra h
    exact hD' (by simp [Function.notMem_support.1 h])
  · intro D'
    exact Nat.zero_le _

/-- The coefficient in `A'` of the component of `F` through `x'` is at
most `m_r(E, A) - m`. (`F` is smooth and lies over `Z`, so at most one component passes
through a point, with coefficient `m_r - m` by `step_spec`.) -/
private theorem coeffAt_step_last_le {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ C.maxStratumWeight r) (x : blowUp (C.stepCenter r)) :
    (C.step m r).coeffAt (Fin.last C.E.s) x ≤ C.maxStratumWeight r - m := by
  classical
  obtain ⟨-, -, -, hmd, -, h6, h7⟩ := C.step_spec hC hk (by omega : 1 ≤ r) hm hmr
  obtain ⟨-, hlft', -, hsnc', -⟩ := hmd
  haveI : LocallyOfFiniteType (C.step m r).sX := hlft'
  set F := (C.step m r).E.E (Fin.last C.E.s)
  have hsm := (hsnc'.2.1 (Fin.last C.E.s)).2.2
  have hF : (F.support : Set (blowUp (C.stepCenter r))) =
      blowUpToBase (C.stepCenter r) ⁻¹' ((C.stepCenter r).support : Set X) := h7 hr
  unfold MonomialData.coeffAt
  by_cases hex : ∃ D : AlgebraicGeometry.PrimeDivisor (blowUp (C.stepCenter r)),
      D.support ∈ componentsOf (F.support : Set _) ∧ x ∈ D.support
  · obtain ⟨D₀, hD₀c, hxD₀⟩ := hex
    rw [finsum_eq_single _ D₀ fun D hD => if_neg fun hDx => hD
      (Aux.PrimeDivisor.eq_of_support_eq (Aux.eq_of_mem_componentsOf_of_isSmoothScheme _ _ hsm
        hDx.1 hD₀c hDx.2 hxD₀))]
    rw [if_pos ⟨hD₀c, hxD₀⟩]
    have hgen : D₀.genericPoint ∈ (D₀.support : Set _) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hgenF : D₀.genericPoint ∈ (F.support : Set _) := hD₀c.1.2 hgen
    rw [hF] at hgenF
    exact (h6 D₀ hgenF).le
  · simp only [not_exists, not_and] at hex
    rw [finsum_eq_zero_of_forall_eq_zero fun D => if_neg fun h => hex D h.1 h.2]
    exact Nat.zero_le _

/-- A sum over `J ⊆ {1, …, n + 1}` splits into the part over `{1, …, n}` and the last term. -/
private theorem sum_eq_sum_castSucc_add {n : ℕ} (J : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → ℕ) : ∑ j ∈ J, f j =
      ∑ i ∈ Finset.univ.filter (fun i => Fin.castSucc i ∈ J), f (Fin.castSucc i) +
        if Fin.last n ∈ J then f (Fin.last n) else 0 := by
  rw [Finset.sum_filter, ← Fin.sum_univ_castSucc (f := fun j => if j ∈ J then f j else 0),
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- A closed subset of a noetherian space has finitely many connected components. -/
private theorem finite_connectedComponentIn {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] {s : Set α} (hs : IsClosed s) :
    {c | ∃ x ∈ s, c = connectedComponentIn s x}.Finite := by
  obtain ⟨S, hSf, -, hSi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine (hSf.biUnion (t := fun t => {c | ∃ y ∈ t, c = connectedComponentIn (⋃₀ S) y})
    fun t ht => ?_).subset ?_
  · refine Set.Subsingleton.finite ?_
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact connectedComponentIn_eq
      ((hSi t ht).2.isPreconnected.subset_connectedComponentIn hy
        (Set.subset_sUnion_of_mem ht) hz)
  · rintro _ ⟨x, ⟨t, ht, hxt⟩, rfl⟩
    exact Set.mem_biUnion ht ⟨x, hxt, rfl⟩

/-- For monomial data there are finitely many pieces of `r`-fold intersections of maximal
weight. -/
private theorem finite_isMaxPiece {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (r : ℕ) :
    {p : Finset (Fin C.E.s) × Set X | C.IsMaxPiece r p.1 p.2}.Finite := by
  obtain ⟨-, hlft, hqc, -⟩ := hC
  haveI : LocallyOfFiniteType C.sX := hlft
  haveI : QuasiCompact C.sX := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian C.sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace C.sX
  haveI : IsNoetherian X := {}
  have hcl : ∀ J, IsClosed (C.stratum J) := fun J =>
    isClosed_biInter fun j _ => (C.E.E j).support.isClosed
  refine ((Set.finite_univ (α := Finset (Fin C.E.s))).biUnion fun J _ =>
    (Set.finite_singleton J).prod (finite_connectedComponentIn (hcl J))).subset ?_
  rintro ⟨J, P⟩ ⟨-, ⟨x, hx, hP⟩, -⟩
  exact Set.mem_biUnion (Set.mem_univ J) ⟨rfl, x, hx, hP⟩

/-- A connected component of a closed set is closed. -/
private theorem isClosed_connectedComponentIn {α : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsClosed s) (x : α) : IsClosed (connectedComponentIn s x) := by
  by_cases hx : x ∈ s
  · refine closure_subset_iff_isClosed.1 ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset _ _) hs)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- Every point of the centre `Z` lies on a maximal piece of `E^{J_*}`. -/
private theorem exists_isMaxPiece_of_mem_stepCenter {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (r : ℕ) {y : X} (hy : y ∈ ((C.stepCenter r).support : Set X)) :
    ∃ P, C.IsMaxPiece r (C.stepIndex r) P ∧ y ∈ P := by
  have hfin : {P | C.IsMaxPiece r (C.stepIndex r) P}.Finite :=
    ((finite_isMaxPiece C hC r).image Prod.snd).subset fun P hP => ⟨(C.stepIndex r, P), hP, rfl⟩
  have hcl : IsClosed (⋃₀ {P | C.IsMaxPiece r (C.stepIndex r) P}) := by
    refine hfin.isClosed_sUnion fun P hP => ?_
    obtain ⟨-, ⟨x, -, rfl⟩, -⟩ := hP
    exact isClosed_connectedComponentIn
      (isClosed_biInter fun j _ => (C.E.E j).support.isClosed) x
  rw [MonomialData.stepCenter, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure, hcl.closure_eq] at hy
  exact hy

/-- The arithmetic of Step 3.`r`: if `y ∈ E^I` lies on a maximal piece of some `E^J`, `|J| = r`,
and `|I| + 1 < r`, then `σ_I(y) + (m_r - m) < m` as soon as `m_t < m` for `1 ≤ t < r`. Indeed,
for `j ∈ J \ I` the left side is at most `σ_{I ∪ {j}}(y) + σ_{J \ {j}}(y) - m`, and both weights
are `< m` since `|I ∪ {j}| = |I| + 1` and `|J \ {j}| = r - 1` are below `r`. -/
private theorem stratumWeight_add_sub_lt {X : Scheme.{u}} (C : MonomialData X)
    (hfin : (Function.support C.A).Finite) {m r : ℕ}
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) {I J : Finset (Fin C.E.s)}
    (hIr : I.card + 1 < r) {P : Set X} (hP : C.IsMaxPiece r J P) {y : X} (hyI : y ∈ C.stratum I)
    (hyP : y ∈ P) : C.stratumWeight I y + (C.maxStratumWeight r - m) < m := by
  classical
  obtain ⟨hJ, ⟨z, -, rfl⟩, hPw⟩ := hP
  have hyJ : y ∈ C.stratum J := connectedComponentIn_subset _ _ hyP
  obtain ⟨j, hjJ, hjI⟩ : ∃ j ∈ J, j ∉ I := Finset.not_subset.1 fun h => by
    have := Finset.card_le_card h; omega
  have hmem : ∀ {K : Finset (Fin C.E.s)}, K ⊆ J ∪ I → y ∈ C.stratum K := fun hK => by
    simp only [MonomialData.stratum, Set.mem_iInter] at hyJ hyI ⊢
    exact fun i hi => (Finset.mem_union.1 (hK hi)).elim (hyJ i) (hyI i)
  have hA := stratumWeight_le_maxStratumWeight C hfin (Finset.card_insert_of_notMem hjI)
    (hmem (Finset.insert_subset (Finset.mem_union_left _ hjJ) Finset.subset_union_right))
  have hB := stratumWeight_le_maxStratumWeight C hfin
    (show (J.erase j).card = r - 1 by rw [Finset.card_erase_of_mem hjJ, hJ])
    (hmem ((Finset.erase_subset _ _).trans Finset.subset_union_left))
  have hσ := hPw y hyP
  have := hlow _ (by omega) hIr
  have := hlow (r - 1) (by omega) (by omega)
  unfold MonomialData.stratumWeight at hA hB hσ ⊢
  rw [Finset.sum_insert hjI] at hA
  rw [← Finset.add_sum_erase _ _ hjJ] at hσ
  omega

/-- Every `t`-fold weight of the new data, `1 ≤ t < r`, is `< m`. -/
private theorem stratumWeight_step_lt {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m)
    (hmr : m ≤ C.maxStratumWeight r) {t : ℕ} (ht1 : 1 ≤ t) (htr : t < r)
    (J : Finset (Fin (C.E.s + 1))) (hJ : J.card = t)
    (x : blowUp (C.stepCenter r)) (hx : x ∈ (C.step m r).stratum J) :
    (C.step m r).stratumWeight J x < m := by
  classical
  have hfin : (Function.support C.A).Finite := hC.2.2.2.2.1
  set π := blowUpToBase (C.stepCenter r)
  set J₀ : Finset (Fin C.E.s) := Finset.univ.filter fun i => Fin.castSucc i ∈ J with hJ₀def
  have hsplit : ∑ j ∈ J, (C.step m r).coeffAt j x =
      ∑ i ∈ J₀, (C.step m r).coeffAt (Fin.castSucc i) x +
        if Fin.last C.E.s ∈ J then
          (C.step m r).coeffAt (Fin.last C.E.s) x else 0 :=
    sum_eq_sum_castSucc_add (n := C.E.s) J fun j => (C.step m r).coeffAt j x
  have hcard : J.card = J₀.card +
      if Fin.last C.E.s ∈ J then 1 else 0 := by
    rw [Finset.card_eq_sum_ones J, Finset.card_eq_sum_ones J₀]
    exact sum_eq_sum_castSucc_add (n := C.E.s) J fun _ => 1
  have hx₀ : π x ∈ C.stratum J₀ := by
    simp only [MonomialData.stratum, Set.mem_iInter] at hx ⊢
    intro i hi
    exact mem_support_of_mem_support_step C m r i (hx (Fin.castSucc i) (Finset.mem_filter.1 hi).2)
  have hle₀ : ∑ i ∈ J₀, (C.step m r).coeffAt (Fin.castSucc i) x ≤ C.stratumWeight J₀ (π x) :=
    Finset.sum_le_sum fun i _ => coeffAt_step_castSucc_le C hC hk hr hm hmr i x
  unfold MonomialData.stratumWeight
  refine hsplit.le.trans_lt ?_
  split_ifs at hcard ⊢ with hl
  · -- the piece involves `F`: `π x ∈ Z ∩ E^{J₀}`, `|J₀| = t - 1`
    have hxZ : π x ∈ ((C.stepCenter r).support : Set X) := by
      have hxF : x ∈ (((C.E.totalTransform (C.stepCenter r)).E (Fin.last C.E.s)).support :
          Set (blowUp (C.stepCenter r))) := by
        simp only [MonomialData.stratum, Set.mem_iInter] at hx
        exact hx _ hl
      rwa [(MonomialData.step_spec C hC hk (by omega : 1 ≤ r) hm hmr).2.2.2.2.2.2 hr] at hxF
    obtain ⟨P, hP, hxP⟩ := exists_isMaxPiece_of_mem_stepCenter C hC r hxZ
    have := stratumWeight_add_sub_lt C hfin hlow (by omega) hP hx₀ hxP
    have := coeffAt_step_last_le C hC hk hr hm hmr x
    omega
  · have := stratumWeight_le_maxStratumWeight C hfin (by omega : J₀.card = t) hx₀
    have := hlow t ht1 htr
    omega

namespace MonomialData

/-- **The Step-3.`r` blow-up preserves `m_t < m` for `t < r`** (Kollár 3.111, Step 3.`r`). For
monomial data `C = (X, E, A)` over a field of characteristic `0`, `2 ≤ r` and
`1 ≤ m ≤ m_r(E, A)` with `m_t(E, A) < m` for all `1 ≤ t < r`, the Step-3.`r` blow-up
`C.step m r` again satisfies `m_t(E', A') < m` for all `1 ≤ t < r`. -/
@[mmp "lem_kr3e_monomial_step_preserves_lower"]
public theorem maxStratumWeight_step_lt {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) (hmr : m ≤ C.maxStratumWeight r) :
    ∀ t, 1 ≤ t → t < r → (C.step m r).maxStratumWeight t < m := by
  intro t ht1 htr
  refine Nat.lt_of_le_sub_one (by omega) <| ciSup_le' fun J => ciSup_le' fun hJ =>
    ciSup_le' fun x => ciSup_le' fun hx => ?_
  exact Nat.le_sub_one_of_lt (stratumWeight_step_lt C hC hk hr hm hlow hmr ht1 htr J hJ x hx)

/-- The induction behind `exists_maxStratumWeight_iterate_lt`, on the value
`p = toLex (m_r, n_r)`. -/
private theorem exists_maxStratumWeight_iterate_lt_aux {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (p : Lex (ℕ × ℕ)) :
    ∀ {X : Scheme.{u}} (C : MonomialData X),
      toLex (C.maxStratumWeight r, C.maxStratumCount r) = p →
      C.IsMonomialData → CharZero C.k →
      (∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) →
      ∃ N : ℕ, ∀ t, 1 ≤ t → t ≤ r → (C.iterate m r N).2.maxStratumWeight t < m := by
  induction p using WellFoundedLT.induction with
  | _ p ih =>
    intro X C hp hC hk hlow
    by_cases hmr : C.maxStratumWeight r < m
    · exact ⟨0, fun t ht1 htr => htr.lt_or_eq.elim (hlow t ht1) (· ▸ hmr)⟩
    · have hmr' : m ≤ C.maxStratumWeight r := not_lt.mp hmr
      obtain ⟨N, hN⟩ := ih _
        (hp ▸ toLex_maxStratumWeight_maxStratumCount_step_lt C hC hk hr hm hlow hmr')
        (C.step m r) rfl (step_spec C hC hk (by omega) hm hmr').2.2.2.1 hk
        (maxStratumWeight_step_lt C hC hk hr hm hlow hmr')
      exact ⟨N + 1, hN⟩

/-- **Step 3.`r` terminates** (Kollár 3.111, Step 3.`r`). For monomial data `C = (X, E, A)` over a
field of characteristic zero, `1 ≤ m` and `2 ≤ r` with `m_t(E, A) < m` for all `1 ≤ t < r`,
iterating the Step-3.`r` blow-up `MonomialData.step m r` reaches, after finitely many steps,
data `C_N = C.iterate m r N` with `m_t(C_N) < m` for all `1 ≤ t ≤ r`. -/
@[mmp "lem_kr3e_monomial_step_r_terminates"]
public theorem exists_maxStratumWeight_iterate_lt {X : Scheme.{u}} (C : MonomialData X)
    (hC : C.IsMonomialData) (hk : CharZero C.k) {m r : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m)
    (hlow : ∀ t, 1 ≤ t → t < r → C.maxStratumWeight t < m) :
    ∃ N : ℕ, ∀ t, 1 ≤ t → t ≤ r → (C.iterate m r N).2.maxStratumWeight t < m :=
  exists_maxStratumWeight_iterate_lt_aux hr hm _ C rfl hC hk hlow

end MonomialData

end MonomialStep

/-! ### Principalization and the entry index -/

section EntryIndex

open AlgebraicGeometry TopologicalSpace CategoryTheory

/-- An ideal is principal iff its inverse image along a ring isomorphism is. -/
private theorem isPrincipal_comap_iso_iff {A B : CommRingCat.{u}} (e : A ≅ B) (J : Ideal B) :
    (J.comap e.hom.hom).IsPrincipal ↔ J.IsPrincipal := by
  have h : J.comap e.hom.hom = J.map e.inv.hom :=
    (Ideal.map_comap_of_equiv (I := J) e.commRingCatIsoToRingEquiv.symm).symm
  exact ⟨fun _ => Ideal.IsPrincipal.of_comap e.hom.hom e.commRingCatIsoToRingEquiv.surjective J,
    fun _ => h ▸ inferInstance⟩

/-- Along an open immersion `f`, the ideal of `I.comap f` on an affine open `W` is principal iff
the ideal of `I` on `f(W)` is. -/
private theorem isPrincipal_ideal_comap_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) (W : X.affineOpens) :
    ((I.comap f).ideal W).IsPrincipal ↔
      (I.ideal ⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩).IsPrincipal := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact isPrincipal_comap_iso_iff (f.appIso W).symm _

/-- Local principality of an ideal sheaf is preserved by inverse image along an open
immersion. -/
private theorem isLocallyPrincipal_comap_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {I : Y.IdealSheafData} (hI : Stacks.Divisors.IsLocallyPrincipal I) :
    Stacks.Divisors.IsLocallyPrincipal (I.comap f) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hI (f x)
  obtain ⟨s, hsle, hxs⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have hD : (I.ideal (Y.affineBasicOpen s)).IsPrincipal := by
    obtain ⟨a, ha⟩ := hU
    rw [← I.map_ideal_basicOpen, ha, Ideal.submodule_span_eq, Ideal.map_span,
      Set.image_singleton]
    exact ⟨_, rfl⟩
  let W : X.affineOpens := ⟨f ⁻¹ᵁ Y.basicOpen s,
    (Y.affineBasicOpen s).2.preimage_of_isOpenImmersion f hsle⟩
  have hW : (⟨f ''ᵁ W, W.2.image_of_isOpenImmersion f⟩ : Y.affineOpens) =
      Y.affineBasicOpen s := by
    apply Subtype.ext
    change f ''ᵁ f ⁻¹ᵁ Y.basicOpen s = Y.basicOpen s
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hsle
  refine ⟨W, hxs, ?_⟩
  rwa [isPrincipal_ideal_comap_iff, hW]

/-- In the specialization order of a scheme, `closure {a} ⊊ closure {b}` means `a < b`. -/
private theorem lt_of_closure_ssubset {X : Scheme.{u}} {a b : X}
    (h : closure {a} ⊂ closure {b}) : a < b := by
  simpa only [lt_iff_le_not_ge, Scheme.le_iff_specializes, specializes_iff_closure_subset]

/-- A strict chain `closure {η} ⊊ Y₁ ⊊ Y₂` of irreducible closed subsets gives
`2 ≤ coheight η`. -/
private theorem two_le_coheight {X : Scheme.{u}} {η : X}
    (h : ∃ Y₁ Y₂ : IrreducibleCloseds X, closure {η} ⊂ (Y₁ : Set X) ∧ (Y₁ : Set X) ⊂ Y₂) :
    2 ≤ Order.coheight η := by
  obtain ⟨Y₁, Y₂, h₁, h₂⟩ := h
  obtain ⟨y₁, hy₁⟩ := QuasiSober.sober Y₁.isIrreducible Y₁.isClosed
  obtain ⟨y₂, hy₂⟩ := QuasiSober.sober Y₂.isIrreducible Y₂.isClosed
  rw [IsGenericPoint] at hy₁ hy₂
  have l₁ : η < y₁ := lt_of_closure_ssubset (hy₁ ▸ h₁)
  have l₂ : y₁ < y₂ := lt_of_closure_ssubset (hy₁ ▸ hy₂ ▸ h₂)
  have e₂ := Order.coheight_add_one_le l₂
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight y₂ + 1 + 1 := by gcongr <;> exact bot_le
    _ ≤ Order.coheight y₁ + 1 := by gcongr
    _ ≤ Order.coheight η := Order.coheight_add_one_le l₁

/-- **Krull's principal ideal theorem, geometric form.** On a locally noetherian scheme, if
`closure {η}` is an irreducible component of the support of an ideal sheaf `I` and has
codimension `≥ 2`, then `I` is not principal on any affine open containing `η`. -/
private theorem not_isPrincipal_ideal_of_two_le_coheight {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {η : X}
    (hη : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X)) (closure {η}))
    (hcodim : 2 ≤ Order.coheight η) (W : X.affineOpens) (hηW : η ∈ W.1) :
    ¬ (I.ideal W).IsPrincipal := by
  intro hprin
  have hW : IsAffineOpen W.1 := W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  set x := hW.primeIdealOf ⟨η, hηW⟩
  have hx : hW.fromSpec x = η := hW.fromSpec_primeIdealOf ⟨η, hηW⟩
  have hsupp : ∀ y : Spec Γ(X, W.1),
      hW.fromSpec y ∈ (I.support : Set X) ↔ (I.ideal W : Set Γ(X, W.1)) ⊆ y.asIdeal := by
    intro y
    have hyW : hW.fromSpec y ∈ W.1 := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨y, rfl⟩
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hyW, ← Set.mem_preimage,
      hW.fromSpec_preimage_zeroLocus]
    rfl
  have hηsupp : η ∈ (I.support : Set X) := hη.prop.2 (subset_closure rfl)
  have hmin : x.asIdeal ∈ (I.ideal W).minimalPrimes := by
    refine ⟨⟨x.isPrime, (hsupp x).mp (hx ▸ hηsupp)⟩, ?_⟩
    rintro q ⟨hq, hJq⟩ hqx
    let y : Spec Γ(X, W.1) := ⟨q, hq⟩
    have hyη : hW.fromSpec y ⤳ η :=
      hx ▸ ((PrimeSpectrum.le_iff_specializes y x).mp hqx).map hW.fromSpec.continuous
    have hcl : closure {hW.fromSpec y} ⊆ closure {η} := by
      refine hη.2 ⟨isIrreducible_singleton.closure, ?_⟩
        (specializes_iff_closure_subset.mp hyη)
      exact I.support.isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr ((hsupp y).mpr hJq))
    have hηy : η ⤳ hW.fromSpec y := specializes_iff_closure_subset.mpr hcl
    rw [← hx] at hηy
    exact (PrimeSpectrum.le_iff_specializes x y).mpr
      (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hηy)
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  rw [idealHeight_eq_coheight _ x,
    show Order.coheight (α := Spec Γ(X, W.1)) x = Order.coheight η from
      (coheight_eq_of_isOpenImmersion (x := x) hW.fromSpec).symm.trans (congrArg _ hx)] at hle
  exact absurd (hcodim.trans hle) (by norm_num)

/-- Truncating a blow-up sequence at its full length does nothing. -/
private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

namespace ClosedBlowupSequence

/-- If a blow-up sequence `B` of a smooth scheme `P` over a field principalizes the ideal sheaf
`I` (i.e. `I.comap B.toBase` is locally principal), and `η` is the generic point of an
irreducible component of `I.support` of codimension `≥ 2` in `P`, then some centre of `B` meets
the fibre over `η`: `B.entryIndex η < B.length`. -/
@[mmp "lem_kr3f_entry_index_finite"]
public theorem entryIndex_lt_length_of_isLocallyPrincipal {k : Type u} [Field k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (hP : MMP.Mori.IsSmoothScheme sP)
    (I : P.IdealSheafData) {η : P}
    (hη : Maximal (fun s : Set P => IsIrreducible s ∧ s ⊆ (I.support : Set P)) (closure {η}))
    (hcodim : ∃ Y₁ Y₂ : IrreducibleCloseds P,
      closure {η} ⊂ (Y₁ : Set P) ∧ (Y₁ : Set P) ⊂ Y₂)
    (B : ClosedBlowupSequence P)
    (hprinc : Stacks.Divisors.IsLocallyPrincipal (I.comap B.toBase)) :
    B.entryIndex η < B.length := by
  have : Smooth sP := hP.smooth
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  refine lt_of_le_of_ne (B.entryIndex_le_length η) fun hj => ?_
  obtain ⟨V, hηV, hiso⟩ :=
    Kollar.exists_isIso_truncate_toBase_restrict_of_le_entryIndex B η B.length hj.ge
  rw [truncate_length] at hiso
  let g : V.toScheme ⟶ B.target := inv (B.toBase ∣_ V) ≫ (B.toBase ⁻¹ᵁ V).ι
  have hg : g ≫ B.toBase = V.ι := by
    simp only [g, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hV : Stacks.Divisors.IsLocallyPrincipal (I.comap V.ι) := by
    rw [← hg, Scheme.IdealSheafData.comap_comp]
    exact isLocallyPrincipal_comap_of_isOpenImmersion g hprinc
  obtain ⟨W, hηW, hW⟩ := hV ⟨η, hηV⟩
  rw [isPrincipal_ideal_comap_iff] at hW
  refine not_isPrincipal_ideal_of_two_le_coheight I hη (two_le_coheight hcodim) _ ?_ hW
  exact ⟨⟨η, hηV⟩, hηW, rfl⟩

end ClosedBlowupSequence

end EntryIndex

end MMP.Resolution
