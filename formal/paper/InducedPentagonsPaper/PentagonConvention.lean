import InducedPentagonsPaper.CycleSymmetry

/-! Canonical pentagon walks are in bijection with induced five-cycle vertex sets. -/

namespace InducedPentagons.Paper

def pentagonVertices {n : Nat} (p : PentagonTuple n) : Finset (Fin n) :=
  Finset.univ.image p.vertex

def CanonicalPentagon {n : Nat} (p : PentagonTuple n) : Prop :=
  p.a < p.b ∧ p.a < p.c ∧ p.a < p.d ∧ p.a < p.e ∧ p.b < p.e

theorem canonicalTuple_iff {n : Nat} (p : PentagonTuple n) :
    canonicalTuple p = true ↔ CanonicalPentagon p := by
  simp only [canonicalTuple, CanonicalPentagon, Bool.and_eq_true_iff,
    decide_eq_true_eq, Fin.lt_def, and_assoc]

theorem mem_inducedPentagons_iff {n : Nat} (g : Graph (Fin n)) (p : PentagonTuple n) :
    p ∈ inducedPentagons g ↔ CanonicalPentagon p ∧ IsInducedPentagon g p.vertex := by
  rw [mem_inducedPentagons]
  simp [normalizedPentagon, canonicalTuple_iff]

theorem inducedPentagons_nodup {n : Nat} (g : Graph (Fin n)) :
    (inducedPentagons g).Nodup := (candidateWalks_nodup g).filter _

theorem pentagonVertices_card {n : Nat} {g : Graph (Fin n)} {p : PentagonTuple n}
    (h : IsInducedPentagon g p.vertex) : (pentagonVertices p).card = 5 := by
  rw [pentagonVertices, Finset.card_image_of_injective _ (inducedPentagon_injective h)]
  simp

theorem pentagonTuple_ext {n : Nat} (p q : PentagonTuple n)
    (h : ∀ i, p.vertex i = q.vertex i) : p = q := by
  simpa using congrArg tupleOfMap (funext h)

def reversePentagon {n : Nat} (p : PentagonTuple n) : PentagonTuple n :=
  ⟨p.a, p.e, p.d, p.c, p.b⟩

@[simp] theorem reversePentagon_vertex {n : Nat} (p : PentagonTuple n) (i : Fin 5) :
    (reversePentagon p).vertex i = p.vertex (cycleReverseIndex i) := by
  fin_cases i <;> rfl

def rotatePentagon {n : Nat} (p : PentagonTuple n) (r : Fin 5) : PentagonTuple n :=
  tupleOfMap (fun i => p.vertex (cycleRotate r i))

@[simp] theorem rotatePentagon_vertex {n : Nat} (p : PentagonTuple n) (r i : Fin 5) :
    (rotatePentagon p r).vertex i = p.vertex (cycleRotate r i) := by
  simp [rotatePentagon]

theorem reindexed_pentagon_vertices {n : Nat} (p q : PentagonTuple n) (f : Fin 5 → Fin 5)
    (hf : Function.Surjective f) (h : ∀ i, q.vertex i = p.vertex (f i)) :
    pentagonVertices q = pentagonVertices p := by
  ext v
  simp only [pentagonVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (h i).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hf i
    exact ⟨j, (h j).trans (congrArg p.vertex hj)⟩

theorem pentagonVertices_reverse {n : Nat} (p : PentagonTuple n) :
    pentagonVertices (reversePentagon p) = pentagonVertices p :=
  reindexed_pentagon_vertices p (reversePentagon p) _ cycleReverse_surjective (reversePentagon_vertex p)

theorem pentagonVertices_rotate {n : Nat} (p : PentagonTuple n) (r : Fin 5) :
    pentagonVertices (rotatePentagon p r) = pentagonVertices p :=
  reindexed_pentagon_vertices p _ _ (cycleRotate_surjective r) (rotatePentagon_vertex p r)

theorem reverse_isInducedPentagon {n : Nat} {g : Graph (Fin n)} {p : PentagonTuple n}
    (hp : IsInducedPentagon g p.vertex) : IsInducedPentagon g (reversePentagon p).vertex := by
  intro i j
  rw [reversePentagon_vertex, reversePentagon_vertex, hp, cycleReverse_pattern]

theorem rotate_isInducedPentagon {n : Nat} {g : Graph (Fin n)} {p : PentagonTuple n}
    (hp : IsInducedPentagon g p.vertex) (r : Fin 5) :
    IsInducedPentagon g (rotatePentagon p r).vertex := by
  intro i j
  rw [rotatePentagon_vertex, rotatePentagon_vertex, hp, cycleRotate_pattern]

theorem canonical_head_le {n : Nat} {p : PentagonTuple n} (hp : CanonicalPentagon p)
    (i : Fin 5) : p.a ≤ p.vertex i := by
  fin_cases i
  · exact le_refl _
  · exact le_of_lt hp.1
  · exact le_of_lt hp.2.1
  · exact le_of_lt hp.2.2.1
  · exact le_of_lt hp.2.2.2.1

theorem exists_canonical_pentagon {n : Nat} {g : Graph (Fin n)} {p : PentagonTuple n}
    (hp : IsInducedPentagon g p.vertex) :
    ∃ q, CanonicalPentagon q ∧ IsInducedPentagon g q.vertex ∧
      pentagonVertices q = pentagonVertices p := by
  obtain ⟨r, _, hr⟩ := Finset.exists_min_image Finset.univ p.vertex (by simp)
  let q := rotatePentagon p r
  have hq : IsInducedPentagon g q.vertex := rotate_isInducedPentagon hp r
  have hmin (i : Fin 5) : q.a ≤ q.vertex i := by
    change (rotatePentagon p r).vertex 0 ≤ (rotatePentagon p r).vertex i
    simpa using hr (cycleRotate r i) (Finset.mem_univ _)
  have hstrict (i : Fin 5) (hi : i ≠ 0) : q.a < q.vertex i := by
    apply lt_of_le_of_ne (hmin i)
    intro he
    change q.vertex 0 = q.vertex i at he
    exact hi ((inducedPentagon_injective hq he).symm)
  have hab : q.a < q.b := hstrict 1 (by decide)
  have hac : q.a < q.c := hstrict 2 (by decide)
  have had : q.a < q.d := hstrict 3 (by decide)
  have hae : q.a < q.e := hstrict 4 (by decide)
  by_cases hbe : q.b < q.e
  · exact ⟨q, ⟨hab, hac, had, hae, hbe⟩, hq, pentagonVertices_rotate p r⟩
  · have hne : q.b ≠ q.e := by
      intro he
      have h14 : (1 : Fin 5) = 4 := inducedPentagon_injective hq he
      norm_num at h14
    have heb : q.e < q.b := lt_of_le_of_ne (le_of_not_gt hbe) hne.symm
    exact ⟨(reversePentagon q), ⟨hae, had, hac, hab, heb⟩, reverse_isInducedPentagon hq,
      (pentagonVertices_reverse q).trans (pentagonVertices_rotate p r)⟩

def InducedPentagonSet {n : Nat} (g : Graph (Fin n)) (s : Finset (Fin n)) : Prop :=
  Nonempty ((toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)))

noncomputable def pentagonTupleIsoOn {n : Nat} {g : Graph (Fin n)} {p : PentagonTuple n}
    (h : IsInducedPentagon g p.vertex) (s : Finset (Fin n)) (hs : pentagonVertices p = s) :
    (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)) where
  toEquiv := Equiv.ofBijective (fun i => ⟨p.vertex i, by rw [← hs]; simp [pentagonVertices]⟩) (by
    constructor
    · intro i j hij
      exact inducedPentagon_injective h (congrArg Subtype.val hij)
    · intro v
      have hv : v.val ∈ pentagonVertices p := by rw [hs]; exact v.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact ⟨i, Subtype.ext hi⟩)
  map_rel_iff' := by
    intro i j
    change g.adj (p.vertex i) (p.vertex j) = true ↔ cycleAdj i j = true
    rw [h]

theorem pentagonTuple_inducedPentagonSet {n : Nat} {g : Graph (Fin n)} {p : PentagonTuple n}
    (h : IsInducedPentagon g p.vertex) : InducedPentagonSet g (pentagonVertices p) :=
  ⟨pentagonTupleIsoOn h _ rfl⟩

noncomputable def tupleOfPentagonIso {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n))) :
    PentagonTuple n := tupleOfMap (fun i => (e i).val)

@[simp] theorem tupleOfPentagonIso_vertex {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n)))
    (i : Fin 5) : (tupleOfPentagonIso e).vertex i = (e i).val := by
  simp [tupleOfPentagonIso]

theorem tupleOfPentagonIso_induced {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n))) :
    IsInducedPentagon g (tupleOfPentagonIso e).vertex := by
  intro i j
  simp only [tupleOfPentagonIso_vertex]
  have h : g.adj (e i).val (e j).val = true ↔ cycleAdj i j = true := e.map_rel_iff
  cases hg : g.adj (e i).val (e j).val <;> cases hp : cycleAdj i j <;> simp_all

theorem tupleOfPentagonIso_vertices {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)}
    (e : (toSimpleGraph cycleGraph) ≃g (toSimpleGraph g).induce (s : Set (Fin n))) :
    pentagonVertices (tupleOfPentagonIso e) = s := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    rw [tupleOfPentagonIso_vertex] at hi
    exact hi ▸ (e i).property
  · intro hv
    obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
      (tupleOfPentagonIso_vertex e i).trans (congrArg Subtype.val hi)⟩

theorem inducedPentagonSet_iff_exists_tuple {n : Nat} {g : Graph (Fin n)} {s : Finset (Fin n)} :
    InducedPentagonSet g s ↔ ∃ p, IsInducedPentagon g p.vertex ∧ pentagonVertices p = s := by
  constructor
  · rintro ⟨e⟩
    exact ⟨tupleOfPentagonIso e, tupleOfPentagonIso_induced e, tupleOfPentagonIso_vertices e⟩
  · rintro ⟨p, hp, rfl⟩
    exact pentagonTuple_inducedPentagonSet hp

theorem inducedPentagonSet_iff_mem_inducedPentagons {n : Nat} {g : Graph (Fin n)}
    {s : Finset (Fin n)} : InducedPentagonSet g s ↔ ∃ p ∈ inducedPentagons g, pentagonVertices p = s := by
  constructor
  · intro hs
    obtain ⟨p, hp, hps⟩ := inducedPentagonSet_iff_exists_tuple.mp hs
    obtain ⟨q, hcan, hq, hqp⟩ := exists_canonical_pentagon hp
    exact ⟨q, (mem_inducedPentagons_iff g q).mpr ⟨hcan, hq⟩, hqp.trans hps⟩
  · rintro ⟨p, hp, rfl⟩
    exact pentagonTuple_inducedPentagonSet ((mem_inducedPentagons_iff g p).mp hp).2

theorem normalized_pentagon_unique {n : Nat} {g : Graph (Fin n)} {p q : PentagonTuple n}
    (hp : IsInducedPentagon g p.vertex) (hq : IsInducedPentagon g q.vertex)
    (hp' : CanonicalPentagon p) (hq' : CanonicalPentagon q)
    (hvs : pentagonVertices p = pentagonVertices q) : p = q := by
  have hhead : p.a = q.a := by
    apply le_antisymm
    · have hmem : q.a ∈ pentagonVertices p := by
        rw [hvs]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact hi ▸ canonical_head_le hp' i
    · have hmem : p.a ∈ pentagonVertices q := by
        rw [← hvs]
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact hi ▸ canonical_head_le hq' i
  let ep := pentagonTupleIsoOn hp (pentagonVertices p) rfl
  let eq := pentagonTupleIsoOn hq (pentagonVertices p) hvs.symm
  let e := ep.trans eq.symm
  have hpoint : ∀ i, q.vertex (e i) = p.vertex i := by
    intro i
    exact congrArg Subtype.val (eq.apply_symm_apply (ep i))
  have hroot : e 0 = 0 := by
    apply inducedPentagon_injective hq
    exact (hpoint 0).trans hhead
  have hrel : ∀ i j, cycleAdj (e i) (e j) = cycleAdj i j := by
    intro i j
    have h : cycleAdj (e i) (e j) = true ↔ cycleAdj i j = true := e.map_rel_iff
    cases h1 : cycleAdj (e i) (e j) <;> cases h2 : cycleAdj i j <;> simp_all
  rcases cycle_rooted_self_maps (fun i => e i) hroot hrel with hid | hrev
  · apply pentagonTuple_ext p q
    intro i
    have h := hpoint i
    rw [hid i] at h
    exact h.symm
  · have h1 := hpoint 1
    have h4 := hpoint 4
    rw [hrev 1] at h1
    rw [hrev 4] at h4
    change q.e = p.b at h1
    change q.b = p.e at h4
    have hback : q.e < q.b := by rw [h1, h4]; exact hp'.2.2.2.2
    exact False.elim ((lt_asymm hq'.2.2.2.2) hback)

theorem inducedPentagons_vertices_injective {n : Nat} (g : Graph (Fin n))
    {p q : PentagonTuple n} (hp : p ∈ inducedPentagons g) (hq : q ∈ inducedPentagons g)
    (hvs : pentagonVertices p = pentagonVertices q) : p = q := by
  have hp' := (mem_inducedPentagons_iff g p).mp hp
  have hq' := (mem_inducedPentagons_iff g q).mp hq
  exact normalized_pentagon_unique hp'.2 hq'.2 hp'.1 hq'.1 hvs

noncomputable def pentagonSubsetEquiv {n : Nat} (g : Graph (Fin n)) :
    ↥(inducedPentagons g).toFinset ≃ {s : Finset (Fin n) // InducedPentagonSet g s} :=
  Equiv.ofBijective (fun p => ⟨pentagonVertices p.val,
    pentagonTuple_inducedPentagonSet
      ((mem_inducedPentagons_iff g p.val).mp (List.mem_toFinset.mp p.property)).2⟩) (by
    constructor
    · intro p q hpq
      apply Subtype.ext
      exact inducedPentagons_vertices_injective g (List.mem_toFinset.mp p.property)
        (List.mem_toFinset.mp q.property) (congrArg Subtype.val hpq)
    · intro s
      obtain ⟨p, hp, he⟩ := inducedPentagonSet_iff_mem_inducedPentagons.mp s.property
      exact ⟨⟨p, List.mem_toFinset.mpr hp⟩, Subtype.ext he⟩)

end InducedPentagons.Paper
