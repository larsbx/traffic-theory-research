set -eu
url=https://data.transportation.gov/resource/8ect-6jqj.csv
pids=""
for k in 0 1 2; do
 start=$((1118936940000+220000*k)); end=$((start+220000))
 curl -fsS --retry 1 --max-time 30 -G "$url" --data-urlencode "\$where=location='lankershim' AND direction='2' AND movement='1' AND global_time >= $start AND global_time < $end AND local_y between 180 and 380 AND (int_id='2' OR section_id='2')" --data-urlencode '$select=vehicle_id,frame_id,global_time,local_y,lane_id,int_id,section_id,v_vel' --data-urlencode '$order=global_time,vehicle_id,frame_id' --data-urlencode '$limit=100000' -o "part$k.csv" &
 pids="$pids $!"
done
for pid in $pids; do wait "$pid"; done
wc -l part?.csv
