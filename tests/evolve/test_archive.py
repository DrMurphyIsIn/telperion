from telperion.evolve.archive import MapElites, Cell


def test_keeps_best_per_cell():
    a = MapElites()
    c = Cell(certifies=True, complexity_bin=1)
    assert a.insert(c, 999.0, "g1") is True
    assert a.insert(c, 998.0, "g_worse") is False   # not better -> no update
    assert a.insert(c, 1000.0, "g_better") is True
    assert a.cells()[c][1] == "g_better"


def test_best_is_global_max():
    a = MapElites()
    a.insert(Cell(True, 1), 999.0, "a")
    a.insert(Cell(True, 3), 997.0, "b")
    a.insert(Cell(False, 0), -300.0, "c")
    score, payload = a.best()
    assert payload == "a" and score == 999.0
