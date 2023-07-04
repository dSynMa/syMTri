int cars_from_left := 0;
int cars_from_right := 0;
bool danger := false;
bool change_direction := false;
output bool closed_from_left := true;
output bool closed_from_right := true;

method extern sensor_update(bool car_from_left_entry, bool car_from_right_entry,
                                bool car_from_left_exit, bool car_from_right_exit,
                                bool _change_direction){
    assume(closed_from_left => !car_from_left_entry);
    assume(closed_from_right => !car_from_right_entry);

    if (car_from_left_entry) cars_from_left++;

    if (car_from_right_entry) cars_from_right++;

    if (car_from_left_exit) cars_from_left--;

    if (car_from_right_exit) cars_from_right--;

    change_direction := _change_direction;

    danger := cars_from_left > 0 && cars_from_right > 0;
}

method intern control(bool close_from_left, bool close_from_right){
    closed_from_left := close_from_left;
    closed_from_right := close_from_right;
}