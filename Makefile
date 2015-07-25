CC := coqc

SRC := $(shell find ./ -type f -name '*.v')
OBJ := $(patsubst %.v, %.vo, $(SRC))

all: $(OBJ)

ArithExpr.vo: ArithExpr.v
	$(CC) $<

clean:
	find ./ -type f -name '*.vo' -delete
	find ./ -type f -name '*.glob' -delete
	find ./ -type f -name '*~' -delete
