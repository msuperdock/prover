function agda-unused $argv
  command agda-unused --root "$NIX_ROOT/src"
end

function with-dir
  set dir (pwd); cd $argv[1]
  eval $argv[2..-1]; set st $status
  cd $dir; return $st
end

function check-agda
  echo; echo 'Checking Agda code:'; echo

  with-dir "$NIX_ROOT/src" \
    agda \
    --local-interfaces \
    --no-libraries \
    --include-path=. \
    Check.agda
  or return $status
  echo 'All done.'

  echo; echo 'Checking for unused code:'; echo
  agda-unused
end

function build-agda
  with-dir "$NIX_ROOT/src" \
    agda \
    --compile \
    --ghc-dont-call-ghc \
    --local-interfaces \
    --no-libraries \
    --include-path=. \
    Main.agda
end

