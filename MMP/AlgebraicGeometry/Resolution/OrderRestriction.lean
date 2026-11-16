module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk

/-!
# Orders of ideals at points; orders do not drop under restriction (Kollár 3.47)

Let `X` be a locally Noetherian scheme, `W ⊆ X` a closed subscheme, `w ∈ W` and `I ⊆ 𝒪_X` an ideal
sheaf. Then `ord_w(I · 𝒪_W) ≥ ord_w I`, and hence `ord_Z(I · 𝒪_W) ≥ ord_Z I` for every irreducible
closed `Z ⊆ W`.

## Main statements

* `MMP.Resolution.Kollar.multAt_le_multAt_comap_subschemeι`: `ord_w I ≤ ord_w(I · 𝒪_W)`; for a
  smooth closed subscheme `S` of a smooth `X` this is also Kollár's `ord_p I ≤ ord_p (I|_S)`.
* `MMP.Resolution.Kollar.orderAlong_le_orderAlong_comap_subschemeι`: `ord_Z I ≤ ord_Z(I · 𝒪_W)`.
* `MMP.Resolution.Kollar.multAt_eq_one_of_finrank_cotangentSpace_lt`: `ord_x I_W = 1` when the
  embedding dimension of `W` at `x` is less than `dim 𝒪_{x,P}` (Kollár 3.47).
* `MMP.Resolution.Kollar.multAt_ne_top_of_stalk_genericPoint_ne_bot`: `ord_x I < ∞` at every
  point when `I` is nonzero at the generic point of every irreducible component of `X`
  (Kollár Def. 3.47: the maximum exists).
* `MMP.Resolution.Kollar.mult_localization_ker_eval_le_of_totalDegree_le`: the order of a
  nonzero polynomial of total degree `≤ d` at a rational point of `𝔸_L^σ` is at most `d`.
* `MMP.Resolution.Kollar.exists_mult_le_mult_localization_ker_eval`: the order of a polynomial
  `P ∈ K[T_1, …, T_N]` at a point `q ∈ 𝔸^N_K` is at most its order at some `L`-rational point,
  for a field extension `L ⊇ K`.

## Implementation notes

The closed subscheme `W` is its ideal sheaf `W : X.IdealSheafData`, with underlying scheme
`W.subscheme` and closed immersion `W.subschemeι : W.subscheme ⟶ X`; the restriction `I · 𝒪_W` is
the pullback `I.comap W.subschemeι`. A point `w ∈ W` is a point of `W.subscheme`, with image
`W.subschemeι w ∈ X`, and an irreducible `Z ⊆ W` is an irreducible subset `Z` of `W.subscheme`,
seen in `X` as its image. The locally Noetherian and closedness hypotheses are not needed and are
dropped.

For the finiteness of `ord_x I`, the source asks for a smooth `X` and a coherent `I` nonzero on
every irreducible component; only local noetherianity is used, and "nonzero on the component `T`"
is read at its generic point, `I_ξ ≠ 0` (for a reduced `X`, as in the source, the two agree).

A point `q` of `𝔸^N_K` is a prime of `K[T_1, …, T_N]`, with local ring `K[T]_q`, and the order of
`P` at `q` is `MMP.Resolution.mult` of its image there. The `L`-rational point `c ∈ L^N` is the
maximal ideal `ker(ev_c)` of `L[T_1, …, T_N]`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace MMP.Resolution.Kollar

private theorem natCast_le_idealOrder_iff {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (m : ℕ) :
    (m : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ m :=
  ⟨le_pow_of_le_idealOrder, fun h => le_iSup₂_of_le m h le_rfl⟩

private theorem idealOrder_le_idealOrder_map {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map φ) := by
  unfold idealOrder
  refine iSup₂_le fun j hj => le_iSup₂_of_le j ?_ le_rfl
  calc I.map φ ≤ (IsLocalRing.maximalIdeal R ^ j).map φ := Ideal.map_mono hj
    _ = ((IsLocalRing.maximalIdeal R).map φ) ^ j := Ideal.map_pow _ _ _
    _ ≤ IsLocalRing.maximalIdeal S ^ j :=
      Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) j

/-- The order of an ideal of a local ring is antitone in the ideal. -/
theorem idealOrder_antitone {R : Type*} [CommRing R] [IsLocalRing R] {J J' : Ideal R}
    (h : J ≤ J') : idealOrder J' ≤ idealOrder J :=
  iSup₂_le fun j hj => le_iSup₂_of_le (f := fun (j : ℕ) (_ : J ≤ IsLocalRing.maximalIdeal R ^ j) =>
    (j : ℕ∞)) j (h.trans hj) le_rfl

open IsLocalRing in
private theorem spanFinrank_maximalIdeal_le_of_surjective {A B : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hker : RingHom.ker f ≤ maximalIdeal A ^ 2) :
    (maximalIdeal A).spanFinrank ≤ (maximalIdeal B).spanFinrank := by
  have := isNoetherianRing_of_surjective A B f hf
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank
    (maximalIdeal B).fg_of_isNoetherianRing
  have hsfin : s.Finite := Set.finite_of_encard_eq_coe hcard
  let t : Set A := Function.surjInv hf '' s
  have hft : f '' t = s := by
    rw [Set.image_image]
    simp [Function.surjInv_eq hf]
  have htfin : t.Finite := hsfin.image _
  have hsm : s ⊆ maximalIdeal B := hs ▸ Submodule.subset_span
  have htm : Ideal.span t ≤ maximalIdeal A := by
    rw [Ideal.span_le]
    intro a ha
    have : f a ∈ maximalIdeal B := hsm (hft ▸ Set.mem_image_of_mem f ha)
    change a ∈ maximalIdeal A
    rw [mem_maximalIdeal, mem_nonunits_iff] at this ⊢
    exact fun h => this (h.map f)
  have hle : maximalIdeal A ≤
      Ideal.span t ⊔ maximalIdeal A • maximalIdeal A := by
    intro a ha
    have h1 : f a ∈ Ideal.map f (Ideal.span t) := by
      rw [Ideal.map_span, hft]
      change f a ∈ Submodule.span B s
      rw [hs, ← map_maximalIdeal_of_surjective f hf]
      exact Ideal.mem_map_of_mem f ha
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp h1
    have h₂ : a - b ∈ maximalIdeal A • maximalIdeal A := by
      have h := hker (show a - b ∈ RingHom.ker f by simp [RingHom.mem_ker, hab])
      rwa [pow_two] at h
    simpa using Submodule.add_mem_sup hb h₂
  have heq : Ideal.span t = maximalIdeal A :=
    le_antisymm htm (Submodule.le_of_le_smul_of_le_jacobson_bot
      (maximalIdeal A).fg_of_isNoetherianRing (maximalIdeal_le_jacobson _) hle)
  calc (maximalIdeal A).spanFinrank = (Ideal.span t).spanFinrank := by rw [heq]
    _ ≤ t.ncard := Submodule.spanFinrank_span_le_ncard_of_finite htfin
    _ ≤ s.ncard := Set.ncard_image_le hsfin
    _ = _ := by
      rw [Set.ncard_def, hcard]
      simp

variable {X : Scheme.{u}} (W I : X.IdealSheafData)

/-- **Kollár, Def. 3.47.** Let `W ⊆ X` be a closed subscheme, `w ∈ W` and `I ⊆ 𝒪_X` an ideal sheaf.
Then `ord_w(I · 𝒪_W) ≥ ord_w I`. -/
@[mmp "lem_kr3c_order_restriction_ge"]
theorem multAt_le_multAt_comap_subschemeι (w : W.subscheme) :
    multAt I (W.subschemeι w) ≤ multAt (I.comap W.subschemeι) w := by
  unfold multAt
  rw [IdealSheafData.stalk_comap]
  exact idealOrder_le_idealOrder_map _ _

/-- **Kollár, Def. 3.47**, "in particular". For every irreducible `Z ⊆ W`,
`ord_Z(I · 𝒪_W) ≥ ord_Z I`. -/
@[mmp "lem_kr3c_order_restriction_ge"]
theorem orderAlong_le_orderAlong_comap_subschemeι {Z : Set W.subscheme} (hZ : IsIrreducible Z) :
    orderAlong I (hZ.image W.subschemeι W.subschemeι.continuous.continuousOn) ≤
      orderAlong (I.comap W.subschemeι) hZ := by
  have h : (hZ.image W.subschemeι W.subschemeι.continuous.continuousOn).genericPoint =
      W.subschemeι hZ.genericPoint := by
    have hc : Continuous W.subschemeι := W.subschemeι.continuous
    refine IsGenericPoint.eq
      (hZ.image W.subschemeι hc.continuousOn).isGenericPoint_genericPoint_closure ?_
    have := hZ.isGenericPoint_genericPoint_closure.image hc
    rwa [closure_image_closure hc] at this
  unfold orderAlong
  rw [h]
  exact multAt_le_multAt_comap_subschemeι W I _

/-- **Kollár, Def. 3.47** (order one). Let `P` be a smooth scheme, `W ⊆ P` a closed subscheme with
ideal sheaf `I_W`, and `x ∈ W` a point with `dim_{κ(x)} 𝔪_{x,W}/𝔪_{x,W}² < dim 𝒪_{x,P}`. Then
`ord_x I_W = 1`. (Smoothness of `P` is used only through the regularity of `𝒪_{x,P}`, which is
assumed instead.) -/
@[mmp "lem_kr3c_order_ideal_of_subscheme_eq_one"]
theorem multAt_eq_one_of_finrank_cotangentSpace_lt (w : W.subscheme)
    [IsRegularLocalRing (X.presheaf.stalk (W.subschemeι w))]
    (hw : (Module.finrank (IsLocalRing.ResidueField (W.subscheme.presheaf.stalk w))
        (IsLocalRing.CotangentSpace (W.subscheme.presheaf.stalk w)) : WithBot ℕ∞) <
      ringKrullDim (X.presheaf.stalk (W.subschemeι w))) :
    multAt W (W.subschemeι w) = 1 := by
  unfold multAt
  set J := IdealSheafData.stalk W (W.subschemeι w)
  let e := IdealSheafData.subschemeStalkQuotEquiv W w
  have hnt : Nontrivial (X.presheaf.stalk (W.subschemeι w) ⧸ J) := e.toEquiv.nontrivial
  have hJtop : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp hnt
  have h1 : (1 : ℕ∞) ≤ idealOrder J := by
    simpa using (natCast_le_idealOrder_iff J 1).mpr
      (by simpa using IsLocalRing.le_maximalIdeal hJtop)
  have h2 : ¬ (2 : ℕ∞) ≤ idealOrder J := by
    intro h
    have h' := (natCast_le_idealOrder_iff J 2).mp (by exact_mod_cast h)
    let f : X.presheaf.stalk (W.subschemeι w) →+* W.subscheme.presheaf.stalk w :=
      e.toRingHom.comp (Ideal.Quotient.mk J)
    have hfs : Function.Surjective f := e.surjective.comp Ideal.Quotient.mk_surjective
    have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal _ ^ 2 := by
      intro a ha
      apply h'
      have : e (Ideal.Quotient.mk J a) = 0 := ha
      rwa [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem] at this
    have hA : IsNoetherianRing (X.presheaf.stalk (W.subschemeι w)) :=
      IsRegularLocalRing.toIsNoetherian
    have hB : IsNoetherianRing (W.subscheme.presheaf.stalk w) :=
      isNoetherianRing_of_surjective _ _ f hfs
    have hle := spanFinrank_maximalIdeal_le_of_surjective f hfs hker
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hle
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace
      (X.presheaf.stalk (W.subschemeι w))).mp inferInstance
    rw [← hreg] at hw
    have hw' : Module.finrank (IsLocalRing.ResidueField (W.subscheme.presheaf.stalk w))
        (IsLocalRing.CotangentSpace (W.subscheme.presheaf.stalk w)) <
        Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk (W.subschemeι w)))
          (IsLocalRing.CotangentSpace (X.presheaf.stalk (W.subschemeι w))) := by
      exact_mod_cast hw
    omega
  exact le_antisymm (by simpa using not_le.mp h2) h1

/- Kollár §3.9, opening (`lem_kr3d_order_le_order_restriction`): for a smooth closed
subscheme `S` of a smooth `X`, `ord_p I ≤ ord_p (I|_S)` (with `ord_p 0 = ∞`). This is the case of
a smooth `S` of `multAt_le_multAt_comap_subschemeι`, which holds for every closed subscheme. -/
attribute [mmp "lem_kr3d_order_le_order_restriction"] multAt_le_multAt_comap_subschemeι

/-- **Kollár, Def. 3.47** (the maximum exists). Let `X` be a locally noetherian scheme and
`I ⊆ 𝒪_X` an ideal sheaf which is nonzero at the generic point of every irreducible component
of `X`. Then `ord_x I < ∞` for every `x ∈ X`. -/
@[mmp "lem_kr3c_order_at_point_finite"]
theorem multAt_ne_top_of_stalk_genericPoint_ne_bot [IsLocallyNoetherian X]
    (hI : ∀ T (hT : T ∈ irreducibleComponents X),
      IdealSheafData.stalk I hT.1.genericPoint ≠ ⊥)
    (x : X) : multAt I x ≠ ⊤ := by
  intro htop
  have hbot : IdealSheafData.stalk I x = ⊥ := by
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal _)
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
    exact le_iInf fun n =>
      (natCast_le_idealOrder_iff _ n).mp (show (n : ℕ∞) ≤ multAt I x by rw [htop]; exact le_top)
  obtain ⟨⟨T, hT⟩, hxT⟩ := MMP.Mori.exists_mem_irreducibleComponents x
  have hTirr := hT.1
  have hgen : IsGenericPoint hTirr.genericPoint T := by
    have := hTirr.isGenericPoint_genericPoint_closure
    rwa [(isClosed_of_mem_irreducibleComponents T hT).closure_eq] at this
  have hξx : hTirr.genericPoint ⤳ x := hgen.specializes hxT
  apply hI T hT
  rw [Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hξx, hbot, Ideal.map_bot]

open MvPolynomial in
/-- **Kollár, Def. 3.47** (reduction of the order of a polynomial to a rational point). Let `K`
be a field, `q` a point of `𝔸^N_K = Spec K[T_1, …, T_N]` and `P ∈ K[T_1, …, T_N]`. There are a
field extension `L ⊇ K` and `c ∈ L^N` such that `ord_q P` is at most the order of `P` at the
`L`-rational point `c`, that is, in the local ring of `L[T_1, …, T_N]` at the kernel of evaluation
at `c`. -/
@[mmp "lem_kr3c_order_polynomial_rational_point_bound"]
theorem exists_mult_le_mult_localization_ker_eval {K : Type u} [Field K] {N : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin N) K)) (P : MvPolynomial (Fin N) K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (c : Fin N → L),
      haveI := RingHom.ker_isPrime (eval c)
      mult (algebraMap _ (Localization.AtPrime q.asIdeal) P) ≤
        mult (algebraMap _ (Localization.AtPrime (RingHom.ker (eval c)))
          (map (algebraMap K L) P)) := by
  let R := MvPolynomial (Fin N) K
  haveI hq : q.asIdeal.IsPrime := q.2
  let L := FractionRing (R ⧸ q.asIdeal)
  let c : Fin N → L := fun i => algebraMap _ L (Ideal.Quotient.mk q.asIdeal (X i))
  have key : ∀ f : R, eval c (map (algebraMap K L) f) =
      algebraMap (R ⧸ q.asIdeal) L (Ideal.Quotient.mk q.asIdeal f) := by
    intro f
    have : (eval c).comp (map (algebraMap K L)) =
      (algebraMap (R ⧸ q.asIdeal) L).comp (Ideal.Quotient.mk q.asIdeal) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp
        rw [IsScalarTower.algebraMap_apply K (R ⧸ q.asIdeal) L]
        rfl
      · simp [c]
        rfl
    exact RingHom.congr_fun this f
  have hker : ∀ f : R, map (algebraMap K L) f ∈ RingHom.ker (eval c) ↔ f ∈ q.asIdeal := by
    intro f
    rw [RingHom.mem_ker, key, map_eq_zero_iff _ (IsFractionRing.injective _ _),
      Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨L, inferInstance, inferInstance, c, ?_⟩
  haveI hp : (RingHom.ker (eval c)).IsPrime := RingHom.ker_isPrime _
  let g := Localization.localRingHom q.asIdeal (RingHom.ker (eval c)) (map (algebraMap K L))
    (Ideal.ext fun f => (hker f).symm)
  have := idealOrder_le_idealOrder_map g
    (Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) P})
  unfold mult
  rwa [Ideal.map_span, Set.image_singleton, Localization.localRingHom_to_map] at this

end MMP.Resolution.Kollar

/-!
## The order of a polynomial at a rational point is at most its degree

Let `L` be a field, `c` an `L`-rational point of `𝔸_L^σ` and `Q ∈ L[T_σ]` a nonzero polynomial of
total degree `≤ d`. Then the order of `Q` at `c` — the largest `r` with `Q` in the `r`-th power
of the maximal ideal of the local ring `L[T]_c` — is at most `d`. Together with
`MMP.Resolution.Kollar.exists_mult_le_mult_localization_ker_eval`, which reduces the order at an
arbitrary point of `𝔸^N_K` to that at a rational point over an extension field, this bounds the
order of a polynomial at every point by its degree (Kollár 3.61).

### Implementation notes

After the translation `T_i ↦ T_i + c_i` the point `c` is the origin, and an element of the
`n`-th power of its maximal ideal has, as a power series, no terms of degree `< n`.

### References

* [J. Kollár, *Lectures on resolution of singularities*, 3.61][kollar2007]
-/

section

open MvPolynomial

variable {σ L : Type*} [Field L]

namespace MMP.Resolution.Kollar

/-- An element outside `𝔪^(d+1)` has order at most `d`. -/
private lemma mult_le_of_notMem_pow {R : Type*} [CommRing R] [IsLocalRing R] {x : R} {d : ℕ}
    (hx : x ∉ IsLocalRing.maximalIdeal R ^ (d + 1)) : mult x ≤ d := by
  refine iSup₂_le fun j hj => ?_
  by_contra hlt
  have hj' : d + 1 ≤ j := by exact_mod_cast Order.add_one_le_of_lt (not_le.mp hlt)
  exact hx (hj.trans (Ideal.pow_le_pow_right hj') (Ideal.mem_span_singleton_self _))

/-- Power series all of whose coefficients in total degree `< n` vanish. -/
private def lowIdeal (σ L : Type*) [Field L] (n : ℕ) : Ideal (MvPowerSeries σ L) where
  carrier := {f | ∀ m : σ →₀ ℕ, m.degree < n → MvPowerSeries.coeff m f = 0}
  zero_mem' := fun m _ => by simp
  add_mem' := by
    intro a b ha hb m hm
    simp [ha m hm, hb m hm]
  smul_mem' := by
    intro a b hb m hm
    classical
    simp only [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := map_add Finsupp.degree p.1 p.2
    rw [hp] at h
    simp [hb p.2 (by omega)]

private lemma lowIdeal_mul_le (a b : ℕ) :
    lowIdeal σ L a * lowIdeal σ L b ≤ lowIdeal σ L (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro f hf g hg m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have h := map_add Finsupp.degree p.1 p.2
  rw [hp] at h
  by_cases h1 : p.1.degree < a
  · simp [hf _ h1]
  · simp [hg p.2 (by omega)]

private lemma lowIdeal_pow_le (n : ℕ) :
    lowIdeal σ L 1 ^ n ≤ lowIdeal σ L n := by
  induction n with
  | zero => intro f _ m hm; omega
  | succ n ih => exact pow_succ (lowIdeal σ L 1) n ▸
      (Ideal.mul_mono_left ih).trans (lowIdeal_mul_le n 1)

/-- A polynomial of total degree `< n` whose power series has no terms of degree `< n` is zero. -/
private lemma eq_zero_of_coe_mem_lowIdeal {p : MvPolynomial σ L} {n : ℕ}
    (hp : p.totalDegree < n) (hmem : (p : MvPowerSeries σ L) ∈ lowIdeal σ L n) : p = 0 := by
  ext m
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hm : m.degree < n
  · simpa [MvPolynomial.coeff_coe] using hmem m hm
  · exact coeff_eq_zero_of_totalDegree_lt (by rw [← Finsupp.degree_apply]; omega)

/-- Translation `T_i ↦ T_i + c_i`. -/
private noncomputable def shift (c : σ → L) : MvPolynomial σ L →ₐ[L] MvPolynomial σ L :=
  aeval fun i => X i + C (c i)

private lemma constantCoeff_shift (c : σ → L) (f : MvPolynomial σ L) :
    constantCoeff (shift c f) = eval c f := by
  have : (constantCoeff.comp (shift c).toRingHom : MvPolynomial σ L →+* L) = eval c := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_) <;> simp [shift]
  exact RingHom.congr_fun this f

private lemma constantCoeff_coe_shift (c : σ → L) (f : MvPolynomial σ L) :
    MvPowerSeries.constantCoeff (shift c f : MvPowerSeries σ L) = eval c f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    ← constantCoeff_eq, constantCoeff_shift]

private lemma shift_injective (c : σ → L) : Function.Injective (shift c) := by
  have : ((aeval fun i => X i - C (c i)).comp (shift c) : MvPolynomial σ L →ₐ[L] _) =
      AlgHom.id L _ :=
    MvPolynomial.algHom_ext fun i => by simp [shift]
  exact Function.LeftInverse.injective (g := aeval fun i => X i - C (c i))
    fun p => DFunLike.congr_fun this p

private lemma totalDegree_shift_le (c : σ → L) (p : MvPolynomial σ L) :
    (shift c p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [shift, aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left (m i) (((totalDegree_add _ _).trans
      (by simp [totalDegree_X, totalDegree_C])) : (X i + C (c i)).totalDegree ≤ 1))) ?_
  simp only [mul_one]
  exact le_totalDegree hm

/-- After translating `c` to the origin, the ideal of `c` lands in `(T) ⊆ K[[T]]`. -/
private lemma coe_shift_mem_lowIdeal_one (c : σ → L) {f : MvPolynomial σ L}
    (hf : f ∈ RingHom.ker (eval c)) : (shift c f : MvPowerSeries σ L) ∈ lowIdeal σ L 1 := by
  intro m hm
  obtain rfl : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_coe_shift]

/-- If `s(c) ≠ 0` and `s Q ∈ 𝔪_c^n`, then the translate of `Q` has no terms of degree `< n`. -/
private lemma coe_shift_mem_lowIdeal_of_mul_mem_pow (c : σ → L) {s Q : MvPolynomial σ L} {n : ℕ}
    (hs : eval c s ≠ 0) (hsQ : s * Q ∈ RingHom.ker (eval c) ^ n) :
    (shift c Q : MvPowerSeries σ L) ∈ lowIdeal σ L n := by
  let Φ : MvPolynomial σ L →+* MvPowerSeries σ L :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp (shift c).toRingHom
  have hJ : (RingHom.ker (eval c)).map Φ ≤ lowIdeal σ L 1 :=
    Ideal.map_le_iff_le_comap.mpr fun f hf => coe_shift_mem_lowIdeal_one c hf
  have hlow : Φ (s * Q) ∈ lowIdeal σ L n := lowIdeal_pow_le n <|
    Ideal.pow_right_mono hJ _ (Ideal.map_pow Φ _ n ▸ Ideal.mem_map_of_mem Φ hsQ)
  obtain ⟨u, hu⟩ : IsUnit (Φ s) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    exact (constantCoeff_coe_shift c s).symm ▸ hs.isUnit
  change Φ Q ∈ _
  rw [show Φ Q = ↑u⁻¹ * Φ (s * Q) by rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]]
  exact Ideal.mul_mem_left _ _ hlow

/-- At an `L`-rational point `c` of `𝔸_L^σ`, the order of a nonzero polynomial of total degree at
most `d` is at most `d`. -/
theorem mult_localization_ker_eval_le_of_totalDegree_le (c : σ → L) {Q : MvPolynomial σ L}
    (hQ : Q ≠ 0) {d : ℕ} (hd : Q.totalDegree ≤ d) :
    haveI := RingHom.ker_isPrime (eval c)
    mult (algebraMap _ (Localization.AtPrime (RingHom.ker (eval c))) Q) ≤ d := by
  haveI := RingHom.ker_isPrime (eval c)
  refine mult_le_of_notMem_pow ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
    IsLocalization.algebraMap_mem_map_algebraMap_iff (RingHom.ker (eval c)).primeCompl]
  rintro ⟨s, hs, hsQ⟩
  refine hQ (shift_injective c ?_)
  rw [map_zero]
  exact eq_zero_of_coe_mem_lowIdeal (by have := totalDegree_shift_le c Q; omega)
    (coe_shift_mem_lowIdeal_of_mul_mem_pow c hs hsQ)

end MMP.Resolution.Kollar

end
