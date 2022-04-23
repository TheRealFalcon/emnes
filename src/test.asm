  JSR init
  JSR loop
  JSR end
init:
  LDA #$03
  RTS
middle:
  LDX #$07
  RTS
end:
  BRK
