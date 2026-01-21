namespace Version

/-- Lem: smoosh_version : string -/
def smoosh_version : String :=
  "0.1"

/-- Lem: smoosh_build : string -/
def smoosh_build : String :=
  "v0.1-265-gcc67dbe"

/-- Lem: smoosh_time : string -/
def smoosh_time : String :=
  "2025-12-18 12:59"

/-- Lem: smoosh_info : string -/
def smoosh_info : String :=
  s!"smoosh v{smoosh_version} (build {smoosh_build} on {smoosh_time})\n"

end Version
