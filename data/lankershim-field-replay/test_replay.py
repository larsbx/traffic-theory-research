import unittest
from replay import START, extract, upstream_stops

def p(f, y, speed=1, lane=2, section="2"):
    return f, y, speed, lane, section

class TestReplay(unittest.TestCase):
    def test_cross_once(self):
        samples = [p(1,349), p(2,350), p(3,349), p(4,351)]
        observed = extract({1: {START + i*100: s for i,s in enumerate(samples)}}, 350)
        self.assertEqual(observed["total"], 1)
        self.assertEqual(observed["bins_30s"][0], 1)

    def test_gap_and_frame_mismatch_not_invented(self):
        tracks = {1: {START:p(1,349), START+200:p(2,351)},
                  2: {START:p(1,349), START+100:p(3,350)}}
        actual = extract(tracks, 350)
        self.assertEqual(actual["total"], 0)
        self.assertEqual(actual["unaccepted_gap_transitions"], 2)

    def test_stopped_proxy_duration(self):
        tracks = {v:{START+i*100:p(i,245, speed) for i in range(n)}
                  for v,n,speed in [(1,31,1),(2,30,1),(3,31,4)]}
        self.assertEqual(upstream_stops(tracks), 1)

if __name__ == "__main__":
    unittest.main()
