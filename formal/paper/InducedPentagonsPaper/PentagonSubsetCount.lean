import InducedPentagonsPaper.PentagonConvention

/-! The normalization by ten is the weighted induced-subset convention on every finite graph. -/

open scoped BigOperators

namespace InducedPentagons.Paper

noncomputable section

abbrev PentagonSets {n : Nat} (g : Graph (Fin n)) :=
  {s : Finset (Fin n) // InducedPentagonSet g s}

instance {n : Nat} (g : Graph (Fin n)) : Fintype (PentagonSets g) := Fintype.ofFinite _

def embeddingVertices {n : Nat} (g : Graph (Fin n)) (p : PentagonEmbedding g) : PentagonSets g :=
  ⟨pentagonVertices (tupleOfMap p.val), pentagonTuple_inducedPentagonSet (by
    simpa using p.property)⟩

def embeddingOfPentagonIso {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)))
    (f : CycleSymmetry) : PentagonEmbedding g :=
  ⟨fun i => (e (f.val i)).val, by
    intro i j
    have h : g.adj (e (f.val i)).val (e (f.val j)).val = true ↔
        cycleAdj (f.val i) (f.val j) = true := e.map_rel_iff
    have hf := f.property i j
    change cycleAdj (f.val i) (f.val j) = cycleAdj i j at hf
    rw [hf] at h
    cases hg : g.adj (e (f.val i)).val (e (f.val j)).val <;>
      cases hc : cycleAdj i j <;> simp_all⟩

theorem embeddingOfPentagonIso_vertices {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)))
    (f : CycleSymmetry) : (embeddingVertices g (embeddingOfPentagonIso e f)).val = s := by
  change Finset.univ.image (fun i => (e (f.val i)).val) = s
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact (e (f.val i)).property
  · intro hv
    obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
    obtain ⟨j, hj⟩ := (cycleSymmetry_bijective f).2 i
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
      rw [hj]
      exact congrArg Subtype.val hi⟩

def embeddingFibreEquiv {n : Nat} (g : Graph (Fin n)) (s : PentagonSets g)
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s.val : Set (Fin n))) :
    {p : PentagonEmbedding g // embeddingVertices g p = s} ≃ CycleSymmetry where
  toFun p := by
    let ep := pentagonTupleIsoOn (p := tupleOfMap p.val.val)
      (by simpa using p.val.property) s.val (congrArg Subtype.val p.property)
    let a := ep.trans e.symm
    refine ⟨fun i => a i, ?_⟩
    intro i j
    change cycleAdj (a i) (a j) = cycleAdj i j
    have h : cycleAdj (a i) (a j) = true ↔ cycleAdj i j = true := a.map_rel_iff
    cases h1 : cycleAdj (a i) (a j) <;> cases h2 : cycleAdj i j <;> simp_all
  invFun f := ⟨embeddingOfPentagonIso e f, Subtype.ext (embeddingOfPentagonIso_vertices e f)⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (e (e.symm ⟨(tupleOfMap p.val.val).vertex i, _⟩)).val = p.val.val i
    rw [e.apply_symm_apply]
    exact congrFun (tupleOfMap_vertex p.val.val) i
  right_inv f := by
    apply Subtype.ext
    funext i
    change e.symm ⟨(tupleOfMap (fun j => (e (f.val j)).val)).vertex i, _⟩ = f.val i
    simp only [tupleOfMap_vertex]
    exact e.symm_apply_apply (f.val i)

theorem embeddingFibre_card {n : Nat} (g : Graph (Fin n)) (s : PentagonSets g) :
    Fintype.card {p : PentagonEmbedding g // embeddingVertices g p = s} = 10 := by
  classical
  exact (Fintype.card_congr (embeddingFibreEquiv g s s.property.some)).trans cycleSymmetry_card

theorem pentagonEmbedding_product {n : Nat} (g : Graph (Fin n))
    (p : PentagonEmbedding g) (x : Fin n → ℝ) :
    (∏ i, x (p.val i)) = ∏ v ∈ (embeddingVertices g p).val, x v := by
  symm
  change (∏ v ∈ Finset.univ.image p.val, x v) = ∏ i, x (p.val i)
  exact Finset.prod_image (inducedPentagon_injective p.property).injOn

def pentagonSetMass {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∑ s : PentagonSets g, ∏ v ∈ s.val, x v

theorem pentagonMass_eq_setMass {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) :
    pentagonMass g x = pentagonSetMass g x := by
  classical
  have hfibre (s : PentagonSets g) :
      (∑ p : {p : PentagonEmbedding g // embeddingVertices g p = s}, ∏ i, x (p.val.val i)) =
        (10 : ℝ) * ∏ v ∈ s.val, x v := by
    calc
      _ = ∑ _p : {p : PentagonEmbedding g // embeddingVertices g p = s},
          ∏ v ∈ s.val, x v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [pentagonEmbedding_product g p.val, p.property]
      _ = _ := by simp [embeddingFibre_card, nsmul_eq_mul]
  unfold pentagonMass pentagonSetMass
  rw [← Fintype.sum_fiberwise (embeddingVertices g) (fun p => ∏ i, x (p.val i))]
  simp_rw [hfibre]
  rw [← Finset.mul_sum]
  ring

theorem pentagonSet_card_eq_normalized_length {n : Nat} (g : Graph (Fin n)) :
    Fintype.card (PentagonSets g) = (inducedPentagons g).length := by
  rw [← Fintype.card_congr (pentagonSubsetEquiv g), Fintype.card_coe]
  exact List.toFinset_card_of_nodup (inducedPentagons_nodup g)

theorem pentagonMass_eq_normalized_length {n : Nat} (g : Graph (Fin n)) :
    pentagonMass g (fun _ => 1) = ((inducedPentagons g).length : ℝ) := by
  rw [pentagonMass_eq_setMass]
  simp [pentagonSetMass, pentagonSet_card_eq_normalized_length]

def normalizedPentagonMass {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ((inducedPentagons g).map (fun p => ∏ i, x (p.vertex i))).sum

theorem pentagonMass_eq_normalizedMass {n : Nat} (g : Graph (Fin n)) (x : Fin n → ℝ) :
    pentagonMass g x = normalizedPentagonMass g x := by
  classical
  rw [pentagonMass_eq_setMass]
  unfold pentagonSetMass normalizedPentagonMass
  rw [← List.sum_toFinset (fun p => ∏ i, x (p.vertex i)) (inducedPentagons_nodup g)]
  rw [← Finset.sum_coe_sort (inducedPentagons g).toFinset (fun p => ∏ i, x (p.vertex i))]
  symm
  apply Fintype.sum_equiv (pentagonSubsetEquiv g)
  intro p
  symm
  change (∏ v ∈ Finset.univ.image p.val.vertex, x v) = ∏ i, x (p.val.vertex i)
  exact Finset.prod_image (inducedPentagon_injective
    ((mem_inducedPentagons_iff g p.val).mp (List.mem_toFinset.mp p.property)).2).injOn

theorem labelled_length_eq_ten_mul_normalized {n : Nat} (g : Graph (Fin n)) :
    (labelledPentagons g).length = 10 * (inducedPentagons g).length := by
  have h := pentagonMass_eq_normalized_length g
  rw [pentagonMass_unit, pentagon_card_eq_labelled_length] at h
  exact_mod_cast (show ((labelledPentagons g).length : ℝ) =
    10 * ((inducedPentagons g).length : ℝ) by linarith)

theorem clebsch_induced_pentagonSet_card : Fintype.card (PentagonSets clebsch) = 192 := by
  have h := pentagonMass_eq_setMass clebsch (fun _ => 1)
  rw [clebsch_pentagonMass_unit] at h
  simp only [pentagonSetMass, Finset.prod_const_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

end

end InducedPentagons.Paper
