#
   gov_graph.cql
   Botetourt County Gov Graph Schema — Categorical formalization of SQLite tables

   Source: gov-graphs/src/loaders/schema.sql (6 tables, Phase 0)

   Design notes:
   - entity_parent self-ref FK requires a sentinel root (the county itself)
     since CQL foreign keys are total functions.
   - NULLable fields (end_date, parent_entity_id) use empty string sentinels.
   - Only structurally relevant fields included; metadata (created_at, etc.) omitted.
*)

typeside Ty = literal {
  java_types
    Str = "java.lang.String"
    Int = "java.lang.Integer"
    Dbl = "java.lang.Double"
  java_fns
    concat : Str, Str -> Str = "(x, y) -> x + y"
  java_constants
    zero : Int = "0"
    zeroDbl : Dbl = "0.0"
    empty : Str = "\"\""
}

schema GovGraph = literal : Ty {

  entities
    Entity           # Government body: elected | board_commission | department | advisory *)
    Person           # Individual holding a role within an entity *)
    Meeting          # A convening of an entity *)
    Document         # Supporting document (agenda, minutes, budget, ordinance) *)
    Motion           # A formal action proposed and voted on at a meeting *)
    BudgetItem       # A line item in a fiscal year budget *)

  foreign_keys
    # Person serves in an Entity *)
    person_entity : Person -> Entity

    # Meeting is held by an Entity *)
    meeting_entity : Meeting -> Entity

    # Document is associated with a Meeting and an Entity *)
    doc_meeting : Document -> Meeting
    doc_entity  : Document -> Entity

    # Motion is proposed at a Meeting *)
    motion_meeting : Motion -> Meeting

    # BudgetItem belongs to an Entity, discussed at a Meeting *)
    budget_entity  : BudgetItem -> Entity
    budget_meeting : BudgetItem -> Meeting

    # Entity hierarchy: parent_entity_id
       The county itself is the root (self-referential: entity_parent(county) = county). *)
    entity_parent : Entity -> Entity

  attributes
    # Entity *)
    entity_id   : Entity -> Str       # slug: "board-of-supervisors" *)
    entity_name : Entity -> Str
    entity_type : Entity -> Str       # elected | board_commission | department | advisory *)
    entity_desc : Entity -> Str

    # Person *)
    person_name  : Person -> Str
    person_role  : Person -> Str      # e.g. "Supervisor, Fincastle District" *)
    person_dist  : Person -> Str      # district name *)

    # Meeting *)
    meeting_date : Meeting -> Str     # ISO date *)
    meeting_type : Meeting -> Str     # regular | special | public_hearing | work_session *)
    meeting_loc  : Meeting -> Str

    # Document *)
    doc_type  : Document -> Str       # agenda | minutes | budget | ordinance | ... *)
    doc_title : Document -> Str

    # Motion *)
    motion_text    : Motion -> Str
    motion_mover   : Motion -> Str
    motion_seconder: Motion -> Str
    motion_outcome : Motion -> Str    # passed | failed | tabled | withdrawn *)
    motion_yes     : Motion -> Int
    motion_no      : Motion -> Int

    # BudgetItem *)
    budget_fy     : BudgetItem -> Str
    budget_desc   : BudgetItem -> Str
    budget_cat    : BudgetItem -> Str   # revenue | expenditure *)
    budget_amount : BudgetItem -> Dbl   # adopted_amount *)

  # Path equation: entity_parent is idempotent at the root.
     For the county root entity: entity_parent(county) = county.
     This is not a schema-level equation (it's instance-specific),
     so we verify it in the test instance instead. *)
}
