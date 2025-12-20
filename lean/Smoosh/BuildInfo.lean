namespace Smoosh.BuildInfo
def version : String := "dev"
def build : String := "local"
def time : String := "unknown"
def info : String := s!"smoosh {version}({build},{time})\n"
end Smoosh.BuildInfo
