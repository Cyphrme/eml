-- Lua filter: convert Pandoc tables from longtable to tabular
-- for twocolumn compatibility.
--
-- Quarto wraps tables in its own \begin{table} float with \caption.
-- We only need to replace longtable → tabular inside that float;
-- adding another table float would nest illegally.

function Table(tbl)
  local doc = pandoc.Pandoc({tbl})
  local latex = pandoc.write(doc, 'latex')

  -- longtable → tabular
  latex = latex:gsub("\\begin{longtable}", "\\begin{tabular}")
  latex = latex:gsub("\\end{longtable}", "\\end{tabular}")

  -- strip longtable-specific header/footer commands
  latex = latex:gsub("\\endfirsthead%s*\n?", "")
  latex = latex:gsub("\\endhead%s*\n?", "")
  latex = latex:gsub("\\endfoot%s*\n?", "")
  latex = latex:gsub("\\endlastfoot%s*\n?", "")

  -- strip longtable captions (Quarto provides its own)
  latex = latex:gsub("\\caption{.-}\\tabularnewline%s*\n?", "")

  return pandoc.RawBlock('latex', latex)
end
