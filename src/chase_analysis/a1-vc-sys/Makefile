# Run copland2xhtml, coplandflow, and coplandvalmeaschase

THYINC	= thy.gli
TSTS	:= $(patsubst %.cop,%.xhtml,$(wildcard *.cop)) \
	   $(patsubst %.html,%.xhtml,$(wildcard *.html)) \
	   $(patsubst %.cop,%_chase.xhtml,$(wildcard *.cop))
CHASE	:= $(patsubst %.cop,%_chase.xhtml,$(wildcard *.cop))
FLOW	:= $(patsubst %.cop,%_flow.xhtml,$(wildcard *.cop))

%.xhtml:	%.cop
	copland2xhtml $(COPLAND2XHTMLFLAGS) $*.cop > $@

%_dist.gli:	%.cop
	copland2distinct -o $*_dist.gli $*.cop

%_chase.xhtml:	%.cop %.gln %_dist.gli $(THYINC)
	coplandvalmeaschase $*.cop > $@

%.gl: %.cop %.gln
	coplandval2measchase -o $*.gli $*.cop
	copland2distinct -o $*_dist.gli $*.cop
	m4 -P $*.gln > $@
	rm $*.gli

%.text: %.gl
	chase -c -o $@ $*.gl

%_tree.xhtml: %.text
	chasetree -o $@ $*.text

%_flow.xhtml:	%.cop
	coplandflow $*.cop > $@

%.cop:	%.html
	htmlpre $*.html > $@

all:	$(TSTS)

chase: $(CHASE)

flow: $(FLOW)

clean:
	-rm $(TSTS)

