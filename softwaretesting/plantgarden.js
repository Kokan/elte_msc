
const plant_name_empty = "<>";
const plant_name_cot   = "<carrot>";
const plant_name_crn   = "<corn>";
const plant_name_tto   = "<tomato>";

const plant_empty = 0;
const plant_cot   = 1;
const plant_crn   = 2;
const plant_tto   = 3;

function valid_task(task)
{
   if (!!task.cot && (task.cot <= 0 || task.cot > 5))
      return false;

   if (!!task.crn && (task.crn <= 0 || task.crn > 5))
      return false;

   if (!!task.tto && (task.tto <= 0 || task.tto > 5))
      return false;
      
   return true;
}

function plant(garden, round_no, task)
{
  if (!!task.cot && task.cot > 0)
  {
     garden[task.cot-1] = {plant: plant_cot, date: round_no };
  }

  if (!!task.crn && task.crn > 0)
  {
     garden[task.crn-1] = {plant: plant_crn, date: round_no };
  }

  if (!!task.tto && task.tto > 0)
  {
     garden[task.tto-1] = {plant: plant_tto, date: round_no };
  }
}

function harvest(garden, round_no)
{
  var cot = 0;
  var crn = 0;
  var tto = 0;

  for (var i = 0; i < 5; ++i)
  {
  switch (garden[i].plant)
  {
   case plant_cot:
     if (garden[i].date + 2 == round_no+1)
        cot = 2;
   break;
   case plant_crn:
     if (garden[i].date + 5 == round_no+1)
        crn = 7;
   break;
   case plant_tto:
     if (garden[i].date + 4 == round_no+1)
        tto = 3;
   break;
  }
  }

  return {
    cot: cot,
    crn: crn,
    tto: tto,
  };
}

module.exports.garden_plant_reap_and_collect = function(number_of_rounds, planting_decisions)
{
  if (number_of_rounds != planting_decisions.length)
  {
    return { error: true };
  }

  var cot = 0;
  var crn = 0;
  var tto = 0;
  garden = Array.from({length: 5}, _ => new Object({name: plant_empty, date: -1}))
  for (var i = 0; i < number_of_rounds; ++i)
  {
     if (!valid_task(planting_decisions[i]))
        return { error: true };

     plant(garden, i, planting_decisions[i]);

     units = harvest(garden, i);

     cot += units.cot;
     crn += units.crn;
     tto += units.tto;
  }


  return {
    cot: cot,
    crn: crn,
    tto: tto,
  };
}

module.exports.create_plant_decision = function(n)
{
 return Array.from({length: n}, _ => new Object());
}
